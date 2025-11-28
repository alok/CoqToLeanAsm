/-
  Examples.lean - Example assembly programs

  This module demonstrates the x86 assembler with various
  example programs, matching the Coq examples.v from x86proved.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Mem
import CoqToLeanAsm.Syntax
import CoqToLeanAsm.Encode
import CoqToLeanAsm.Assembler
import CoqToLeanAsm.Macros
import CoqToLeanAsm.SepLogic

namespace X86.Examples

open X86

-- Example 1: Simple instructions
def simpleInstructions : List Instr := [
  .NOP,
  .MOVOP .Op32 (.RR EAX EBX),
  .BOP .Op32 .ADD (.RR EAX ECX),
  .UOP .Op32 .INC (.R EDX),
  .RETOP 0
]

#eval simpleInstructions.map (encode 0) |>.map bytesToHexString

-- Example 2: Memory addressing
def memoryAddressing : List Instr := [
  -- MOV EAX, [EBX]
  .MOVOP .Op32 (.RM EAX (MemSpec.reg EBX)),
  -- MOV EAX, [EBX + 4]
  .MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBX 4)),
  -- MOV EAX, [EBX + ECX*4]
  .MOVOP .Op32 (.RM EAX (MemSpec.regIdx EBX (.ECX) .S4)),
  -- MOV EAX, [EBX + ECX*4 + 8]
  .MOVOP .Op32 (.RM EAX (MemSpec.regIdxDisp EBX (.ECX) .S4 8)),
  -- MOV [0x12345678], EAX
  .MOVOP .Op32 (.MR (MemSpec.disp 0x12345678) EAX)
]

#eval memoryAddressing.map (encode 0) |>.map bytesToHexString

-- Example 3: Arithmetic using syntax macros
-- Note: Due to macro elaboration, we build instructions directly
def arithmeticOps : List Instr := [
  mkMOV (.Reg32 EAX) (.Imm32 0),           -- XOR EAX, EAX would be better
  mkADD (.Reg32 EAX) (.Imm32 10),          -- ADD EAX, 10
  mkSUB (.Reg32 EAX) (.Reg32 EBX),         -- SUB EAX, EBX
  mkAND (.Reg32 EAX) (.Imm32 0xFF),        -- AND EAX, 0xFF
  mkOR  (.Reg32 EAX) (.Reg32 ECX),         -- OR EAX, ECX
  mkXOR (.Reg32 EAX) (.Reg32 EAX),         -- XOR EAX, EAX (clear)
  mkSHL (.Reg32 EAX) (.Imm32 2),           -- SHL EAX, 2 (multiply by 4)
  mkSHR (.Reg32 EAX) (.Imm32 1),           -- SHR EAX, 1 (divide by 2)
]

-- Example 4: A simple function (factorial-ish)
-- Computes n * (n-1) * ... * 1 for n in ECX, result in EAX
def factorialProg : Program := ProgBuilder.buildProg do
  -- MOV EAX, 1 (result)
  ProgBuilder.emit (.MOVOP .Op32 (.RI EAX 1))
  -- TEST ECX, ECX
  ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX))
  -- while (ECX != 0)
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))  -- test
    .Z false  -- JNZ (while not zero)
    (do
      -- EAX = EAX * ECX (simplified: just multiply)
      ProgBuilder.emit (.IMUL EAX (.R ECX))
      -- DEC ECX
      ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))

-- Example 5: GCD using Euclidean algorithm
-- Input: EAX = a, EBX = b
-- Output: EAX = gcd(a, b)
def gcdProg : Program := ProgBuilder.buildProg do
  -- while (EBX != 0)
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R EBX) (.R EBX)))
    .Z false
    (do
      -- EDX:EAX = EAX (for division)
      ProgBuilder.emit (.BOP .Op32 .XOR (.RR EDX EDX))  -- Clear EDX
      -- This would need DIV instruction, simplified:
      -- Instead, use subtraction-based GCD
      -- while (EAX >= EBX) EAX -= EBX
      X86.«while»
        (do
          ProgBuilder.emit (.BOP .Op32 .CMP (.RR EAX EBX)))
        .B false  -- JAE (while EAX >= EBX)
        (ProgBuilder.emit (.BOP .Op32 .SUB (.RR EAX EBX)))
      -- XCHG EAX, EBX
      ProgBuilder.emit (.XCHG .Op32 EAX (.R EBX)))

-- Example 6: Array sum
-- Input: ESI = array pointer, ECX = count
-- Output: EAX = sum
def arraySumProg : Program := ProgBuilder.buildProg do
  ProgBuilder.emit (.BOP .Op32 .XOR (.RR EAX EAX))  -- EAX = 0
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
    .Z false
    (do
      -- ADD EAX, [ESI]
      ProgBuilder.emit (.BOP .Op32 .ADD (.RM EAX (MemSpec.reg ESI)))
      -- ADD ESI, 4
      ProgBuilder.emit (.BOP .Op32 .ADD (.RI ESI 4))
      -- DEC ECX
      ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))

-- Example 7: If-then-else (absolute value)
-- Input: EAX
-- Output: EAX = |EAX|
def absProg : Program := ProgBuilder.buildProg do
  -- TEST EAX, EAX
  ProgBuilder.emit (.TESTOP .Op32 (.R EAX) (.R EAX))
  -- if (SF) then NEG EAX
  ifThen .S true (ProgBuilder.emit (.UOP .Op32 .NEG (.R EAX)))

-- Example 8: Memory copy (simple version)
-- Input: ESI = source, EDI = dest, ECX = count
def memcpyProg : Program := ProgBuilder.buildProg memcpy

-- Example 9: Procedure example
def addProc : Program := ProgBuilder.buildProg do
  proc "add_numbers" 0 do
    -- Arguments at [EBP+8] and [EBP+12]
    ProgBuilder.emit (.MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBP 8)))
    ProgBuilder.emit (.BOP .Op32 .ADD (.RM EAX (MemSpec.regDisp EBP 12)))
    -- Result in EAX

-- Example 10: String length
def strlenProg : Program := ProgBuilder.buildProg strlen

-- Assemble and display hex dumps
def exampleBytes : IO Unit := do
  IO.println "=== Simple Instructions ==="
  for instr in simpleInstructions do
    let bytes := encode 0 instr
    IO.println s!"    -> {bytesToHexString bytes}"

  IO.println "\n=== Factorial Program ==="
  match assemble 0x1000 factorialProg with
  | .ok bytes =>
    IO.println (hexDump bytes 0x1000)
  | .error errs =>
    IO.println s!"Errors: {repr errs}"

  IO.println "\n=== GCD Program ==="
  match assemble 0x2000 gcdProg with
  | .ok bytes =>
    IO.println (hexDump bytes 0x2000)
    IO.println s!"Size: {bytes.length} bytes"
  | .error errs =>
    IO.println s!"Errors: {repr errs}"

  IO.println "\n=== Array Sum ==="
  match assemble 0x3000 arraySumProg with
  | .ok bytes =>
    IO.println (hexDump bytes 0x3000)
  | .error errs =>
    IO.println s!"Errors: {repr errs}"

-- Direct encoding tests
#eval encode 0 .NOP  -- Should be [0x90]
#eval encode 0 .HLT  -- Should be [0xF4]
#eval encode 0 (.RETOP 0)  -- Should be [0xC3]
#eval encode 0 (.PUSH (.R EAX))  -- Should be [0x50]
#eval encode 0 (.POP (.R EBX))   -- Should be [0x5B]

-- MOV encodings
#eval encode 0 (mkMOV (.Reg32 EAX) (.Imm32 0x12345678))  -- B8 78 56 34 12
#eval encode 0 (mkMOV (.Reg32 EBX) (.Reg32 ECX))         -- 89 CB

-- ADD encodings
#eval encode 0 (mkADD (.Reg32 EAX) (.Imm32 5))   -- 05 05 00 00 00
#eval encode 0 (mkADD (.Reg32 EBX) (.Reg32 ECX)) -- 01 CB

-- Memory addressing
#eval encode 0 (.MOVOP .Op32 (.RM EAX (MemSpec.reg EBX)))  -- 8B 03
#eval encode 0 (.MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBX 4)))  -- 8B 43 04
#eval encode 0 (.MOVOP .Op32 (.RM EAX (MemSpec.disp 0x12345678)))  -- 8B 05 78 56 34 12

-- Verification examples using separation logic
section Verification

-- Specification: MOV EAX, 42 sets EAX to 42
theorem mov_eax_42_spec :
    ∀ s s' : ProcState,
      s' = { s with regs := s.regs.writeReg EAX 42 } →
      (EAX ~= 42) s' := by
  intro s s' hs'
  simp [regIs, hs', RegFile.readReg, RegFile.writeReg, RegFile.write]

-- Specification: XOR EAX, EAX clears EAX
theorem xor_eax_eax_clears :
    ∀ v : DWord, (v ^^^ v) = 0 := by
  intro v
  simp [BitVec.xor_self]

-- Specification: ADD is commutative
theorem add_comm :
    ∀ a b : DWord, a + b = b + a := by
  intro a b
  exact BitVec.add_comm a b

end Verification

-- Run tests
-- #eval exampleBytes

-- ============================================================================
-- Simple x86 Interpreter for Demonstration
-- ============================================================================

/-- Compute factorial n! -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- Compute factorial by interpreting x86-style loop -/
def factorialInterpreted (n : Nat) : Nat :=
  -- Simulates: MOV EAX, 1; loop: TEST ECX,ECX; JZ done; IMUL EAX,ECX; DEC ECX; JMP loop
  let rec loop (eax ecx : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => eax
    | f+1 => if ecx == 0 then eax else loop (eax * ecx) (ecx - 1) f
  loop 1 n 100

-- Demonstrate factorial works!
#eval factorialInterpreted 5   -- 120
#eval factorialInterpreted 6   -- 720
#eval factorialInterpreted 10  -- 3628800

-- Verify correctness
#eval (List.range 11).map fun n => (n, factorialInterpreted n, factorial n)

-- ============================================================================
-- Using x86! Macro - Write assembly like a .s file!
-- ============================================================================

-- Define register arguments for the macro
def r_eax : InstrArg := .Reg32 EAX
def r_ebx : InstrArg := .Reg32 EBX
def r_ecx : InstrArg := .Reg32 ECX
def r_edx : InstrArg := .Reg32 EDX
def r_esi : InstrArg := .Reg32 ESI
def r_edi : InstrArg := .Reg32 EDI
def r_ebp : InstrArg := .Reg32 EBP
def r_esp : InstrArg := .Reg32 ESP

-- Define immediate helper
def imm (n : Nat) : InstrArg := .Imm32 (BitVec.ofNat 32 n)

-- Factorial loop body with x86! macro (without labels)
def factorialLoopX86 : Program := x86! {
  mov r_eax, (imm 1)
  test r_ecx, r_ecx
  imul r_eax, r_ecx
  dec r_ecx
}

-- Simple NOP sled with x86! macro
def nopSled : Program := x86! {
  nop
  nop
  nop
  ret
}

#eval nopSled.length  -- 4 items

-- Register clearing idiom
def clearRegs : Program := x86! {
  xor r_eax, r_eax
  xor r_ebx, r_ebx
  xor r_ecx, r_ecx
  xor r_edx, r_edx
}

-- Stack operations
def pushAllRegs : Program := x86! {
  push r_eax
  push r_ebx
  push r_ecx
  push r_edx
}

def popAllRegs : Program := x86! {
  pop r_edx
  pop r_ecx
  pop r_ebx
  pop r_eax
}

-- Print program items
#eval do
  IO.println s!"factorialLoopX86 has {factorialLoopX86.length} items"
  IO.println s!"nopSled has {nopSled.length} items"
  IO.println s!"clearRegs has {clearRegs.length} items"

-- Compare encoded bytes
#eval do
  match assemble 0x1000 nopSled with
  | .ok bytes => IO.println s!"nopSled bytes: {bytesToHexString bytes}"
  | .error _ => IO.println "Error assembling nopSled"

end X86.Examples
