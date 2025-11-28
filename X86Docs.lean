/-
  X86Docs.lean - Documentation for CoqToLeanAsm

  This is a Verso-based documentation site for the x86 macro assembler
  ported from Coq to Lean 4.
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open X86

set_option pp.rawOnError true

#doc (Manual) "CoqToLeanAsm: x86 Macro Assembler in Lean 4" =>

%%%
authors := ["Ported from Kennedy, Benton, Jensen, Dagand (PPDP 2013)"]
%%%

This is a Lean 4 port of "Coq: The World's Best Macro Assembler?" by
Andrew Kennedy, Nick Benton, Jonas Jensen, and Pierre-Évariste Dagand.
The original paper appeared at PPDP 2013 and demonstrated how to use Coq's
dependent types and tactic system to build a verified x86-32 assembler.

# Overview

This library provides a complete {deftech}_x86-32 macro assembler_ implemented in Lean 4,
leveraging dependent types for type-safe {deftech}_instruction encoding_ and assembly.

## Why a Verified Assembler?

Traditional assemblers like NASM, GAS, or MASM are trusted components in the toolchain.
When they produce incorrect output, the resulting bugs are extremely difficult to diagnose
because the generated code doesn't match the source. A verified assembler provides:

1. *Correctness by construction*: The encoding functions are total and deterministic.
   Each instruction variant maps to exactly one byte sequence.

2. *Type-level guarantees*: Lean's type system prevents invalid instruction combinations
   at compile time. You cannot accidentally use ESP as a SIB index register.

3. *Proved properties*: Key encoding properties can be proved using `rfl` (definitional
   equality), giving mathematical certainty about the output.

4. *Executable specification*: The assembler serves as both documentation and
   implementation—the specification *is* the code.

## Key Features

The assembler provides:

- *Bit-precise types* using Lean 4's {lean}`BitVec` for {lean}`Byte`, {lean}`Word`, and {lean}`DWord`
- *Full x86-32 register model* including {lean}`Reg`, {lean}`ByteReg`, and {lean}`SegReg`
- *Comprehensive {tech}[instruction encoding]* with {deftech}_ModR/M byte_ and {deftech}_SIB byte_ generation
- *Separation logic predicates* via {lean}`SPred` for reasoning about memory and registers
- *Multi-pass assembler* with the {lean}`assemble` function for forward reference resolution
- *Control flow macros* including {lean}`ifThenElse`, {lean}`X86.while`, and {lean}`proc`
- *Intel-style syntax* via the `x86!` macro for readable assembly programs

## Design Philosophy

The assembler uses dependent types to ensure correctness:

1. *Type-safe {deftech}_operand sizes_*: The {lean}`OpSize` type indexes register and
   immediate types via {lean}`VWord` and {lean}`VReg`, preventing mismatched {tech}[operand sizes].
   An 8-bit register cannot be used where a 32-bit operand is expected.

2. *Structured {deftech}_addressing modes_*: Memory operands use {lean}`MemSpec`,
   which captures the full range of x86 addressing: base, index, {deftech}_scale factor_, displacement.
   The {lean}`NonSPReg` type statically prevents using ESP as an index register.

3. *Verified encoding*: Each {lean}`Instr` variant maps to exactly one encoding via {lean}`encode`.
   These encodings can be verified against real assembler output using `rfl` proofs.

4. *Compositional assembly*: Programs are built from instruction sequences using
   {lean}`ProgBuilder`, which handles label allocation and forward reference resolution.

# Quick Start

## Installation

Add this package to your `lakefile.toml`:

```
[[require]]
name = "CoqToLeanAsm"
git = "https://github.com/your-repo/CoqToLeanAsm"
```

Then import the main module:

```
import CoqToLeanAsm
open X86
```

## Basic Examples

Here are simple examples encoding x86 instructions:

```lean
-- Basic instructions encode to their expected bytes
#eval encode 0 Instr.NOP        -- [0x90]
#eval encode 0 (Instr.RETOP 0)  -- [0xC3]
#eval encode 0 Instr.HLT        -- [0xF4]
```

# Module Structure

The codebase is organized into focused modules:

*`CoqToLeanAsm.Bits`* — {lean}`Byte`, {lean}`Word`, {lean}`DWord`, {lean}`OpSize`

*`CoqToLeanAsm.Reg`* — {lean}`Reg`, {lean}`ByteReg`, {lean}`SegReg`, {lean}`VReg`

*`CoqToLeanAsm.Instr`* — {lean}`Instr`, {lean}`MemSpec`, {lean}`DstSrc`, {lean}`BinOp`

*`CoqToLeanAsm.Mem`* — {lean}`Memory`, {lean}`Flags`, {lean}`RegFile`, {lean}`ProcState`

*`CoqToLeanAsm.Encode`* — {lean}`encode`, {lean}`encodeInstr`

*`CoqToLeanAsm.SepLogic`* — {lean}`SPred`, {lean}`regIs`, {lean}`dwordIs`

*`CoqToLeanAsm.Macros`* — {lean}`ifThenElse`, {lean}`X86.while`, {lean}`proc`

*`CoqToLeanAsm.Assembler`* — {lean}`assemble`, {lean}`Program`, {lean}`LabelMap`

# Bit Vector Types

The foundation of the assembler is the {lean}`BitVec` type from Lean's standard library.

## Standard Sizes

```lean
#check (Byte : Type)   -- BitVec 8
#check (Word : Type)   -- BitVec 16
#check (DWord : Type)  -- BitVec 32
```

## Operand Size Type

The {lean}`OpSize` type captures x86 operand sizes:

```lean
#check OpSize.Op8   -- 8-bit operations
#check OpSize.Op16  -- 16-bit operations
#check OpSize.Op32  -- 32-bit operations (default in protected mode)
```

The {lean}`VWord` type family maps {lean}`OpSize` to {lean}`BitVec`:

```lean
-- VWord .Op8  = BitVec 8
-- VWord .Op16 = BitVec 16
-- VWord .Op32 = BitVec 32
#check (VWord OpSize.Op32)
```

## Byte Operations

```lean
-- Convert byte to hex string
#check Byte.toHex

-- Extract bytes from DWord (little-endian, index 0 = LSB)
#check DWord.toByte

-- Construct DWord from bytes
#check DWord.fromBytes
```

# Registers

The x86-32 architecture has a rich register set modeled with precise Lean types.

## General Purpose Registers

The eight 32-bit {deftech}_general purpose registers_ (GPRs) are defined by {lean}`Reg`:

```lean
#check EAX  -- Accumulator (encoding 0)
#check ECX  -- Counter (encoding 1)
#check EDX  -- Data (encoding 2)
#check EBX  -- Base (encoding 3)
#check ESP  -- Stack Pointer (encoding 4)
#check EBP  -- Base Pointer (encoding 5)
#check ESI  -- Source Index (encoding 6)
#check EDI  -- Destination Index (encoding 7)
```

The {lean}`NonSPReg` type excludes {lean}`ESP`, which cannot be used as an index in {tech}[SIB byte] addressing.

Each register's encoding is accessed via {lean}`Reg.toNat`:

```lean
#eval EAX.toNat  -- 0
#eval ECX.toNat  -- 1
#eval ESP.toNat  -- 4
```

## Byte Registers

The 8-bit registers defined by {lean}`ByteReg` access low/high bytes of AX, BX, CX, DX:

```lean
-- Low bytes (bits 0-7)
#check AL   -- Low byte of EAX
#check CL   -- Low byte of ECX (used for shift counts)

-- High bytes (bits 8-15)
#check AH   -- High byte of EAX
#check CH   -- High byte of ECX
```

Use {lean}`ByteReg.toReg` to get the parent 32-bit register:

```lean
#eval AL.toReg  -- EAX
```

## Word Registers

16-bit registers via {lean}`WordReg` access the lower 16 bits:

```lean
#check AX   -- Lower 16 bits of EAX
#check DX   -- Lower 16 bits of EDX
```

## Segment Registers

x86 segmentation uses {lean}`SegReg`:

```lean
#check CS   -- Code Segment
#check DS   -- Data Segment
#check SS   -- Stack Segment
#check ES   -- Extra Segment
#check FS   -- Additional Segment (386+)
#check GS   -- Additional Segment (386+)
```

## Variable-Width Registers

The {lean}`VReg` type family selects the appropriate register type based on {lean}`OpSize`:

```lean
-- VReg .Op8  = ByteReg
-- VReg .Op16 = WordReg
-- VReg .Op32 = Reg
#check (VReg OpSize.Op8)
```

# Instructions

The x86 instruction set is represented by the {lean}`Instr` inductive type.

## Instruction Categories

- {lean}`Instr.MOVOP` - Data movement
- {lean}`Instr.BOP` - Binary ALU operations (ADD, SUB, AND, OR, XOR, CMP)
- {lean}`Instr.UOP` - Unary operations (INC, DEC, NOT, NEG)
- {lean}`Instr.SHIFTOP` - Shift and rotate
- {lean}`Instr.JCCrel` - Conditional jumps
- {lean}`Instr.JMPrel` - Unconditional jump
- {lean}`Instr.CALLrel` - Procedure call
- {lean}`Instr.RETOP` - Return from procedure
- {lean}`Instr.PUSH` / {lean}`Instr.POP` - Stack operations

## Memory Addressing

x86's complex {tech}[addressing modes] are captured by {lean}`MemSpec`:

```lean
-- Register indirect: [EBX]
#check MemSpec.reg EBX

-- Register + displacement: [EBX + 8]
#check MemSpec.regDisp EBX 8

-- Absolute address: [0x12345678]
#check MemSpec.disp 0x12345678

-- Scaled index: [EAX + ECX*4]
#check MemSpec.regIdx EAX (NonSPReg.ECX) Scale.S4

-- Full SIB: [EAX + ECX*4 + 16]
#check MemSpec.regIdxDisp EAX (NonSPReg.ECX) Scale.S4 16
```

{tech}[Scale factor]s are defined by {lean}`Scale`:
- {lean}`Scale.S1` - multiply by 1 (no scaling)
- {lean}`Scale.S2` - multiply by 2
- {lean}`Scale.S4` - multiply by 4 (common for 32-bit arrays)
- {lean}`Scale.S8` - multiply by 8 (common for 64-bit arrays)

## Operand Types

### {lean}`DstSrc` - Destination-Source Pairs

For two-operand instructions:

```lean
#check DstSrc.RR  -- reg, reg
#check DstSrc.RM  -- reg, [mem]
#check DstSrc.MR  -- [mem], reg
#check DstSrc.RI  -- reg, imm
#check DstSrc.MI  -- [mem], imm
```

### {lean}`RegMem` - Register or Memory

```lean
#check RegMem.R   -- Register operand
#check RegMem.M   -- Memory operand
```

### {lean}`Src` - Source Operand

```lean
#check Src.I   -- Immediate value
#check Src.R   -- Register
#check Src.M   -- Memory
```

## Data Movement Examples

```lean
-- MOV reg, reg: MOV EAX, EBX
#check Instr.MOVOP OpSize.Op32 (DstSrc.RR EAX EBX)

-- MOV reg, imm: MOV EAX, 42
#check Instr.MOVOP OpSize.Op32 (DstSrc.RI EAX 42)

-- MOV reg, mem: MOV EAX, [EBX]
#check Instr.MOVOP OpSize.Op32 (DstSrc.RM EAX (MemSpec.reg EBX))

-- MOV mem, reg: MOV [EBX], EAX
#check Instr.MOVOP OpSize.Op32 (DstSrc.MR (MemSpec.reg EBX) EAX)

-- PUSH reg
#check Instr.PUSH (Src.R EAX)

-- PUSH imm
#check Instr.PUSH (Src.I 100)

-- POP reg
#check Instr.POP (RegMem.R EBX)
```

## Arithmetic Operations

Binary operations use {lean}`BinOp`:

```lean
#check BinOp.ADD  -- Addition
#check BinOp.SUB  -- Subtraction
#check BinOp.AND  -- Bitwise AND
#check BinOp.OR   -- Bitwise OR
#check BinOp.XOR  -- Bitwise XOR
#check BinOp.CMP  -- Compare (SUB without storing result)
#check BinOp.ADC  -- Add with carry
#check BinOp.SBB  -- Subtract with borrow
```

Examples:

```lean
-- ADD EAX, EBX
#check Instr.BOP OpSize.Op32 BinOp.ADD (DstSrc.RR EAX EBX)

-- SUB EAX, 10
#check Instr.BOP OpSize.Op32 BinOp.SUB (DstSrc.RI EAX 10)

-- XOR EAX, EAX (zero a register)
#check Instr.BOP OpSize.Op32 BinOp.XOR (DstSrc.RR EAX EAX)
```

Unary operations use {lean}`UnaryOp`:

```lean
-- INC ECX
#check Instr.UOP OpSize.Op32 UnaryOp.INC (RegMem.R ECX)

-- DEC ECX
#check Instr.UOP OpSize.Op32 UnaryOp.DEC (RegMem.R ECX)

-- NEG EAX (two's complement)
#check Instr.UOP OpSize.Op32 UnaryOp.NEG (RegMem.R EAX)
```

## Control Flow

Conditional jumps use {lean}`Condition` and a polarity flag:

```lean
-- Conditions
#check Condition.Z   -- Zero/Equal (ZF=1)
#check Condition.B   -- Below/Carry (CF=1)
#check Condition.S   -- Sign (SF=1)
#check Condition.O   -- Overflow (OF=1)
#check Condition.L   -- Less (signed: SF≠OF)
#check Condition.LE  -- Less or Equal (signed)
#check Condition.BE  -- Below or Equal (unsigned)
```

```lean
-- JZ label (jump if zero, polarity=true means jump when condition is true)
#check Instr.JCCrel Condition.Z true

-- JNZ label (jump if not zero, polarity=false inverts)
#check Instr.JCCrel Condition.Z false

-- JMP label (unconditional jump)
#check Instr.JMPrel

-- CALL label (procedure call)
#check Instr.CALLrel

-- RET (return from procedure)
#check Instr.RETOP 0

-- RET 8 (pop 8 extra bytes before return)
#check Instr.RETOP 8
```

# Encoding

x86 {tech}[instruction encoding] is notoriously complex, with variable-length instructions
and multiple encoding options for the same operation. The {lean}`encode` function handles
all details, producing the exact same bytes as a production assembler like NASM.

## Instruction Format

A typical x86 instruction has the following structure:

```
[Prefix] Opcode [ModR/M] [SIB] [Displacement] [Immediate]
```

- *Prefix* (0-4 bytes): Operand size override (0x66), address size override (0x67),
  segment override, REP/REPNE, LOCK
- *Opcode* (1-3 bytes): The operation to perform
- *ModR/M* (0-1 bytes): Specifies register and addressing mode
- *SIB* (0-1 bytes): Scale-Index-Base for complex addressing
- *Displacement* (0, 1, 2, or 4 bytes): Memory offset
- *Immediate* (0, 1, 2, or 4 bytes): Constant operand

## {tech}[ModR/M byte] in Detail

The {tech}[ModR/M byte] is the key to understanding x86 encoding. It packs three fields
into a single byte:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
|  mod  |   reg/op  |    r/m    |
+---+---+---+---+---+---+---+---+
```

*mod* (bits 7-6) specifies the {tech}[addressing modes]:
- `00` = Memory, no displacement (except special cases)
- `01` = Memory + 8-bit signed displacement
- `10` = Memory + 32-bit displacement
- `11` = Register-to-register (no memory access)

*reg/op* (bits 5-3) holds either:
- A register number (0-7) for two-operand instructions
- An opcode extension for single-operand instructions (like INC, DEC, PUSH)

*r/m* (bits 2-0) specifies the destination:
- With mod=11: register number (0-7)
- With mod≠11: addressing mode (100=SIB follows, 101=disp32 with mod=00)

### Register Encoding Table

| Register | Encoding | As r/m with mod=11 |
|----------|----------|-------------------|
| EAX/AX/AL | 000 (0) | Direct register |
| ECX/CX/CL | 001 (1) | Direct register |
| EDX/DX/DL | 010 (2) | Direct register |
| EBX/BX/BL | 011 (3) | Direct register |
| ESP/SP/AH | 100 (4) | *SIB byte follows* |
| EBP/BP/CH | 101 (5) | *disp32 if mod=00* |
| ESI/SI/DH | 110 (6) | Direct register |
| EDI/DI/BH | 111 (7) | Direct register |

### Example: MOV EAX, EBX (0x89 0xD8)

```lean
-- MOV EAX, EBX encodes as [0x89, 0xD8]
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RR EAX EBX))
```

Breaking down `0xD8`:
- Binary: `11 011 000`
- mod = 11 (register-to-register)
- reg = 011 (EBX = 3, the source)
- r/m = 000 (EAX = 0, the destination)

### Example: MOV EBX, EAX (0x89 0xC3)

```lean
-- MOV EBX, EAX encodes as [0x89, 0xC3]
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RR EBX EAX))
```

Breaking down `0xC3`:
- Binary: `11 000 011`
- mod = 11 (register-to-register)
- reg = 000 (EAX = 0, the source)
- r/m = 011 (EBX = 3, the destination)

## {tech}[SIB byte] in Detail

When the r/m field is 100 (would be ESP) with mod≠11, the processor expects a
{tech}[SIB byte] to follow. This enables scaled indexed addressing:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
| scale |   index   |   base    |
+---+---+---+---+---+---+---+---+
```

*scale* (bits 7-6) is the {tech}[scale factor]:
- `00` = ×1
- `01` = ×2
- `10` = ×4
- `11` = ×8

*index* (bits 5-3) is the index register (ESP=100 means "no index")

*base* (bits 2-0) is the base register (EBP=101 with mod=00 means "disp32 only")

### Example: Scaled Index Addressing (0x8B 0x04 0x8B)

```lean
-- MOV EAX, [EBX + ECX*4] encodes as [0x8B, 0x04, 0x8B]
#eval encode 0 (Instr.MOVOP OpSize.Op32
  (DstSrc.RM EAX (MemSpec.regIdx EBX (.ECX) Scale.S4)))
```

Breaking down:
- `0x8B` = MOV r32, r/m32 opcode
- `0x04` = ModR/M: mod=00 (memory), reg=000 (EAX), r/m=100 (SIB follows)
- `0x8B` = SIB: scale=10 (×4), index=001 (ECX), base=011 (EBX)

### Example: Scaled Index with Displacement (0x8B 0x44 0x8B 0x10)

```lean
-- With 8-bit displacement
#eval encode 0 (Instr.MOVOP OpSize.Op32
  (DstSrc.RM EAX (MemSpec.regIdxDisp EBX (.ECX) Scale.S4 16)))
```

- `0x8B` = MOV r32, r/m32 opcode
- `0x44` = ModR/M: mod=01 (memory+disp8), reg=000 (EAX), r/m=100 (SIB)
- `0x8B` = SIB: scale=10 (×4), index=001 (ECX), base=011 (EBX)
- `0x10` = displacement (16 as signed byte)

## Encoding Verification with `rfl`

A key advantage of this implementation is that encodings can be *proved* correct
at compile time using definitional equality:

```lean
-- These theorems are provable by reflexivity!
theorem nop_is_0x90 : encode 0 Instr.NOP = [0x90] := rfl
theorem ret_is_0xC3 : encode 0 (Instr.RETOP 0) = [0xC3] := rfl
theorem hlt_is_0xF4 : encode 0 Instr.HLT = [0xF4] := rfl
```

This means the type checker itself verifies that our encoding matches the expected bytes.

## More Encoding Examples

```lean
-- ADD EAX, imm32 uses special short encoding
-- ADD EAX, 0x12345678 = 05 78 56 34 12
#eval encode 0 (Instr.BOP OpSize.Op32 BinOp.ADD (DstSrc.RI EAX 0x12345678))

-- XOR EAX, EAX (common idiom to zero a register)
-- Shorter than MOV EAX, 0 (2 bytes vs 5 bytes)
#eval encode 0 (Instr.BOP OpSize.Op32 BinOp.XOR (DstSrc.RR EAX EAX))

-- PUSH EBP = 0x55 (uses short encoding 50+rd)
#eval encode 0 (Instr.PUSH (Src.R EBP))

-- MOV EBP, ESP = 0x89 0xE5
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RR EBP ESP))
```

# Control Flow Macros

High-level control flow constructs that expand to instruction sequences.

## The {lean}`ProgBuilder` Monad

Programs are built using {lean}`ProgBuilder`, which tracks:
- Emitted instructions via {lean}`ProgBuilder.emit`
- Label definitions via {lean}`ProgBuilder.label`
- A fresh label counter

```lean
#check ProgBuilder
#check ProgBuilder.emit
#check ProgBuilder.label
```

Build a complete program with {lean}`ProgBuilder.buildProg`:

```lean
#check ProgBuilder.buildProg
```

## {lean}`ifThenElse`

Generates conditional branching:

```lean
#check ifThenElse
#check ifThen
```

Pattern:
```
  ; test (sets flags)
  Jcc else_label
  ; then code
  JMP end_label
else_label:
  ; else code
end_label:
```

## {lean}`X86.while`

Loop construct:

```lean
#check X86.«while»
#check doWhile
```

Pattern:
```
loop_start:
  ; test (sets flags)
  Jcc loop_end
  ; body
  JMP loop_start
loop_end:
```

## {lean}`proc`

Procedure with stack frame:

```lean
#check proc
#check procPrologue
#check procEpilogue
```

Generates:
```
  PUSH EBP
  MOV EBP, ESP
  SUB ESP, frameSize
  ; body
  MOV ESP, EBP
  POP EBP
  RET
```

# Memory Model

## {lean}`Memory`

Memory is modeled as a function from addresses to bytes:

```lean
#check Memory.empty      -- All zeros
#check Memory.readByte   -- Read single byte
#check Memory.writeByte  -- Write single byte
#check Memory.readDWord  -- Read 32-bit value (little-endian)
#check Memory.writeDWord -- Write 32-bit value
```

## {lean}`Flags`

The EFLAGS register:

```lean
#check Flags.CF  -- Carry flag
#check Flags.ZF  -- Zero flag
#check Flags.SF  -- Sign flag
#check Flags.OF  -- Overflow flag
#check Flags.PF  -- Parity flag
#check Flags.DF  -- Direction flag
```

## {lean}`ProcState`

Full processor state combining registers, flags, and memory:

```lean
#check ProcState.empty
#check ProcState.eip     -- Get instruction pointer
#check ProcState.setEIP  -- Set instruction pointer
#check ProcState.push    -- Push to stack
#check ProcState.pop     -- Pop from stack
```

# Assembly

## The {lean}`assemble` Function

Multi-pass assembly with label resolution:

```lean
#check assemble
```

Takes a base address and {lean}`Program`, returns either bytes or errors.

## {lean}`Program` Type

A program is a list of labeled instructions:

```lean
#check Program
```

# Examples with `x86!` Macro

The best way to write assembly is with the `x86!` macro, which provides
Intel-style syntax that looks like a `.s` file.

## Setup: Register Arguments

First, define register operands for the macro:

```
open X86.Examples  -- provides eax, ebx, ecx, edx, imm
```

Or define them yourself:

```
def eax : InstrArg := .Reg32 EAX
def imm (n : Nat) : InstrArg := .Imm32 (BitVec.ofNat 32 n)
```

## Your First Program

A simple NOP sled with return:

```
def helloAsm : Program := x86! {
  nop           -- 0x90
  nop
  ret           -- 0xC3
}
```

## Register Operations

Clear registers using XOR (standard idiom):

```
def clearRegs : Program := x86! {
  xor eax, eax
  xor ebx, ebx
}
```

Arithmetic operations:

```
def arithmetic : Program := x86! {
  mov eax, (imm 42)   -- Load immediate
  add eax, ebx        -- EAX += EBX
  sub eax, ecx        -- EAX -= ECX
  shl eax, (imm 2)    -- EAX *= 4
}
```

## Stack Operations

Save and restore registers:

```
def saveRegs : Program := x86! {
  push eax
  push ebx
  push ecx
  push edx
}

def restoreRegs : Program := x86! {
  pop edx   -- Reverse order!
  pop ecx
  pop ebx
  pop eax
}
```

## Supported Instructions

- *No-operand*: `nop`, `ret`, `hlt`
- *One-operand*: `push`, `pop`, `inc`, `dec`, `not`, `neg`, `mul`
- *Two-operand*: `mov`, `add`, `sub`, `and`, `or`, `xor`, `cmp`, `test`,
  `imul`, `xchg`, `shl`, `shr`, `lea`
- *Jumps*: `jmp`, `call`, `jz`, `jnz`, `je`, `jne`, `jl`, `jge`, `jle`,
  `jg`, `jb`, `jae`, `jbe`, `ja`

# Executable Verification

Verify correctness by interpreting the assembly logic. Our GCD example uses
the Euclidean subtraction algorithm:

```lean
#eval Nat.gcd 48 18    -- 6
#eval Nat.gcd 1071 462 -- 21
```

The GCD algorithm produces correct results matching Lean's built-in {lean}`Nat.gcd`.

# Type Safety

One of the key benefits of embedding an assembler in a dependently-typed language
is that many invalid programs are rejected at compile time.

## Preventing ESP as SIB Index

In x86, the ESP register *cannot* be used as an index in SIB addressing. The encoding
`index=100` (which would be ESP) instead means "no index register." Traditional
assemblers catch this as a runtime error. We catch it at compile time:

The {name}`NonSPReg` type is defined as a subtype of {name}`Reg` that excludes ESP:

```lean
#check NonSPReg       -- Registers excluding ESP
#check NonSPReg.EAX   -- Valid
#check NonSPReg.ECX   -- Valid
#check NonSPReg.EBX   -- Valid
-- NonSPReg.ESP doesn't exist!
```

The {name}`MemSpec.regIdx` constructor requires a {name}`NonSPReg` for the index:

```lean
-- This compiles: ECX is a valid index register
#check MemSpec.regIdx EBX (.ECX) Scale.S4

-- This would NOT compile:
-- #check MemSpec.regIdx EBX (.ESP) Scale.S4
-- Error: NonSPReg has no constructor ESP
```

## Operand Size Consistency

The {name}`OpSize` type ensures operand sizes are consistent across an instruction.
You cannot mix 8-bit and 32-bit operands:

```lean
-- Valid: 32-bit operation with 32-bit registers
#check Instr.BOP OpSize.Op32 BinOp.ADD (DstSrc.RR EAX EBX)

-- Valid: 8-bit operation with 8-bit registers
#check Instr.BOP OpSize.Op8 BinOp.ADD (DstSrc.RR AL BL)
```

The {name}`VReg` and {name}`VWord` type families enforce this:

```lean
#check (VReg OpSize.Op32)  -- = Reg (32-bit registers like EAX)
#check (VReg OpSize.Op8)   -- = ByteReg (8-bit registers like AL)
```

## Immediate Size Checking

Immediate values are checked to fit within their declared size:

```lean
-- 8-bit immediate must fit in a byte
#check (42 : VWord OpSize.Op8)    -- OK: 42 < 256

-- The BitVec type ensures proper truncation/overflow behavior
#check (0xFF : VWord OpSize.Op8)  -- OK: maximum byte value
```

## Label Resolution

Labels in the assembler are managed through structured types to ensure
forward references are correctly resolved:

```lean
#check LabelMap     -- Maps label names to addresses
#check LabelRef     -- Reference to a label (for forward refs)
#check LabelGen     -- Generates fresh labels
```

# Common Assembly Idioms

## Zeroing a Register

The standard idiom to zero a register is XOR with itself:

```lean
-- XOR EAX, EAX is shorter than MOV EAX, 0
-- 2 bytes: 31 C0
-- vs 5 bytes: B8 00 00 00 00
#eval encode 0 (Instr.BOP OpSize.Op32 BinOp.XOR (DstSrc.RR EAX EAX))
```

## Function Prologue and Epilogue

Standard cdecl function setup:

```
-- Prologue (3 bytes)
push ebp        ; 55
mov ebp, esp    ; 89 E5

-- Epilogue (3 bytes)
mov esp, ebp    ; 89 EC
pop ebp         ; 5D
ret             ; C3
```

With the `x86!` macro:

```
def prologue : Program := x86! {
  push ebp
  mov ebp, esp
}

def epilogue : Program := x86! {
  mov esp, ebp
  pop ebp
  ret
}
```

## Comparison with NASM

Our assembler produces identical output to NASM. Given this NASM source:

```
; NASM assembly
section .text
global _start
_start:
    xor eax, eax      ; 31 C0
    mov ebx, 42       ; BB 2A 00 00 00
    add eax, ebx      ; 01 D8
    ret               ; C3
```

Our Lean code produces the same bytes:

```lean
-- Assembles to: 31 C0 BB 2A 00 00 00 01 D8 C3
def nasmExample : List Instr := [
  .BOP .Op32 .XOR (.RR EAX EAX),
  .MOVOP .Op32 (.RI EBX 42),
  .BOP .Op32 .ADD (.RR EAX EBX),
  .RETOP 0
]
```

# Semantic Properties

Beyond correct encoding, we can prove semantic properties of instructions.

## XOR Self Produces Zero

```lean
-- For any 32-bit value v, v XOR v = 0
-- This justifies the "xor eax, eax" idiom
theorem xor_self_zero (v : DWord) : v ^^^ v = 0 := BitVec.xor_self
```

## Subtraction Self Produces Zero

```lean
theorem sub_self_zero (v : DWord) : v - v = 0 := BitVec.sub_self v
```

## Addition is Commutative

```lean
theorem add_comm (a b : DWord) : a + b = b + a := BitVec.add_comm a b
```

These properties let us reason about program behavior, not just encoding correctness.

# References

- Kennedy, Benton, Jensen, Dagand. "Coq: The World's Best Macro Assembler?" PPDP 2013
- Intel 64 and IA-32 Architectures Software Developer's Manual
- x86proved: https://github.com/msr-quarc/x86proved

