/-
  Examples.lean - x86 Assembly Walkthrough

  This module demonstrates the x86 assembler with a progressive tutorial,
  starting from basic concepts and building up to complete programs.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Syntax
import CoqToLeanAsm.Encode
import CoqToLeanAsm.Assembler

namespace X86.Examples

open X86

-- ============================================================================
-- Part 1: Register Arguments for x86! Macro
-- ============================================================================
-- The x86! macro uses InstrArg values for operands. Define shortcuts:

def eax : InstrArg := .Reg32 EAX
def ebx : InstrArg := .Reg32 EBX
def ecx : InstrArg := .Reg32 ECX
def edx : InstrArg := .Reg32 EDX
def esi : InstrArg := .Reg32 ESI
def edi : InstrArg := .Reg32 EDI
def ebp : InstrArg := .Reg32 EBP
def esp : InstrArg := .Reg32 ESP

-- Immediate value helper
def imm (n : Nat) : InstrArg := .Imm32 (BitVec.ofNat 32 n)

-- ============================================================================
-- Part 2: Your First x86! Program
-- ============================================================================
-- Write assembly that looks like a .s file!

def helloAsm : Program := x86! {
  nop           -- No operation (0x90)
  nop
  ret           -- Return (0xC3)
}

#eval helloAsm.length  -- 3 instructions

-- Assemble to bytes:
#eval do
  match assemble 0x1000 helloAsm with
  | .ok bytes => IO.println s!"Bytes: {bytesToHexString bytes}"
  | .error _ => IO.println "Assembly failed"

-- ============================================================================
-- Part 3: Basic Instructions
-- ============================================================================

-- Clear a register (XOR with itself is the standard idiom)
def clearEax : Program := x86! {
  xor eax, eax
}

-- Load immediate value
def loadImmediate : Program := x86! {
  mov eax, (imm 42)
  mov ebx, (imm 0xFF)
}

-- Register-to-register operations
def regOps : Program := x86! {
  mov eax, ebx        -- Copy EBX to EAX
  add eax, ecx        -- EAX += ECX
  sub eax, edx        -- EAX -= EDX
  xor eax, eax        -- Clear EAX
}

-- ============================================================================
-- Part 4: Stack Operations
-- ============================================================================

-- Save registers to stack (caller-save convention)
def saveRegs : Program := x86! {
  push eax
  push ebx
  push ecx
  push edx
}

-- Restore registers (reverse order!)
def restoreRegs : Program := x86! {
  pop edx
  pop ecx
  pop ebx
  pop eax
}

-- ============================================================================
-- Part 5: Arithmetic Examples
-- ============================================================================

-- Double a value: EAX *= 2
def doubleEax : Program := x86! {
  add eax, eax
}

-- Multiply by 5: EAX = EAX * 4 + EAX
def multiplyBy5 : Program := x86! {
  mov ebx, eax        -- Save original
  shl eax, (imm 2)    -- EAX *= 4
  add eax, ebx        -- EAX += original
}

-- ============================================================================
-- Part 6: Encoding Verification
-- ============================================================================
-- Let's verify the assembler produces correct x86 machine code:

-- NOP = 0x90
#eval encode 0 Instr.NOP

-- RET = 0xC3
#eval encode 0 (Instr.RETOP 0)

-- PUSH EAX = 0x50 (single-byte encoding)
#eval encode 0 (Instr.PUSH (.R EAX))

-- MOV EAX, 42 = B8 2A 00 00 00 (opcode + imm32 little-endian)
#eval encode 0 (mkMOV (.Reg32 EAX) (.Imm32 42))

-- XOR EAX, EAX = 31 C0 (opcode 31, ModR/M C0 = 11 000 000)
#eval encode 0 (Instr.BOP .Op32 .XOR (.RR EAX EAX))

-- ============================================================================
-- Part 7: Complete Program - Factorial
-- ============================================================================
-- Computes n! where n is in ECX, result in EAX

-- The core loop (without control flow):
def factorialBody : Program := x86! {
  mov eax, (imm 1)    -- EAX = 1 (accumulator)
  test ecx, ecx       -- Set flags based on ECX
  imul eax, ecx       -- EAX *= ECX
  dec ecx             -- ECX--
}

-- Interpreter to verify the algorithm works:
def factorialInterpreted (n : Nat) : Nat :=
  let rec loop (acc count : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f+1 => if count == 0 then acc else loop (acc * count) (count - 1) f
  loop 1 n 100

-- Test it!
#eval factorialInterpreted 5   -- 120
#eval factorialInterpreted 6   -- 720
#eval factorialInterpreted 10  -- 3628800

-- ============================================================================
-- Part 8: Memory Addressing
-- ============================================================================
-- x86 supports complex addressing modes. Here's how to use them directly:

-- MOV EAX, [EBX] - load from address in EBX
#eval encode 0 (Instr.MOVOP .Op32 (.RM EAX (MemSpec.reg EBX)))

-- MOV EAX, [EBX + 4] - load with displacement
#eval encode 0 (Instr.MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBX 4)))

-- MOV EAX, [EBX + ECX*4] - scaled index addressing
#eval encode 0 (Instr.MOVOP .Op32 (.RM EAX (MemSpec.regIdx EBX (.ECX) .S4)))

-- ============================================================================
-- Part 9: Assembly Output
-- ============================================================================

#eval do
  IO.println "=== Assembled Programs ==="

  IO.println "\nhelloAsm:"
  match assemble 0x1000 helloAsm with
  | .ok bytes => IO.println s!"  {bytesToHexString bytes}"
  | .error _ => IO.println "  Error"

  IO.println "\nclearEax:"
  match assemble 0x1000 clearEax with
  | .ok bytes => IO.println s!"  {bytesToHexString bytes}"
  | .error _ => IO.println "  Error"

  IO.println "\nsaveRegs:"
  match assemble 0x1000 saveRegs with
  | .ok bytes => IO.println s!"  {bytesToHexString bytes}"
  | .error _ => IO.println "  Error"

  IO.println "\ndoubleEax:"
  match assemble 0x1000 doubleEax with
  | .ok bytes => IO.println s!"  {bytesToHexString bytes}"
  | .error _ => IO.println "  Error"

-- ============================================================================
-- Part 10: Verification Theorems
-- ============================================================================

-- XOR x, x always produces 0
theorem xor_self_zero : ∀ v : DWord, (v ^^^ v) = 0 := by
  intro v; simp [BitVec.xor_self]

-- ADD is commutative
theorem add_comm : ∀ a b : DWord, a + b = b + a := by
  intro a b; exact BitVec.add_comm a b

end X86.Examples
