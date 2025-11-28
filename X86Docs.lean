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

This library provides a complete x86-32 macro assembler implemented in Lean 4,
leveraging dependent types for type-safe instruction encoding and assembly.

## Key Features

The assembler provides:

- *Bit-precise types* using Lean 4's {lean}`BitVec` for {lean}`Byte`, {lean}`Word`, and {lean}`DWord`
- *Full x86-32 register model* including {lean}`Reg`, {lean}`ByteReg`, and {lean}`SegReg`
- *Comprehensive instruction encoding* with ModR/M and SIB byte generation
- *Separation logic predicates* via {lean}`SPred` for reasoning about memory and registers
- *Multi-pass assembler* with the {lean}`assemble` function for forward reference resolution
- *Control flow macros* including {lean}`ifThenElse`, {lean}`X86.while`, and {lean}`proc`

## Design Philosophy

The assembler uses dependent types to ensure correctness:

1. *Type-safe operand sizes*: The {lean}`OpSize` type indexes register and
   immediate types via {lean}`VWord` and {lean}`VReg`, preventing mismatched operand sizes.

2. *Structured addressing modes*: Memory operands use {lean}`MemSpec`,
   which captures the full range of x86 addressing: base, index, scale, displacement.

3. *Verified encoding*: Each {lean}`Instr` variant maps to exactly one encoding via {lean}`encode`.

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

The eight 32-bit general purpose registers are defined by {lean}`Reg`:

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

The {lean}`NonSPReg` type excludes {lean}`ESP`, which cannot be used as an index in SIB addressing.

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

x86's complex addressing modes are captured by {lean}`MemSpec`:

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

Scale factors are defined by {lean}`Scale`:
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

x86 instruction encoding is complex. The {lean}`encode` function handles all details.

## Instruction Format

A typical x86 instruction:

```
[Prefix] Opcode [ModR/M] [SIB] [Displacement] [Immediate]
```

## ModR/M Byte

The ModR/M byte specifies register/memory operands:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
|  mod  |   reg/op  |    r/m    |
+---+---+---+---+---+---+---+---+
```

- *mod* (bits 7-6): Addressing mode (00=mem, 01=mem+disp8, 10=mem+disp32, 11=reg)
- *reg/op* (bits 5-3): Register or opcode extension
- *r/m* (bits 2-0): Register/memory operand

## SIB Byte

When r/m=100 (ESP) with mod≠11, a SIB byte follows:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
| scale |   index   |   base    |
+---+---+---+---+---+---+---+---+
```

This enables `[base + index*scale + disp]` addressing.

## Encoding Examples

```lean
-- NOP = 0x90
#eval encode 0 Instr.NOP

-- RET = 0xC3
#eval encode 0 (Instr.RETOP 0)

-- MOV EAX, EBX = 89 D8
-- Opcode 89, ModR/M D8 (mod=11, reg=EBX=3, r/m=EAX=0)
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RR EAX EBX))

-- MOV EAX, 42 = B8 2A 00 00 00
-- Opcode B8+rd, immediate 42 little-endian
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RI EAX 42))

-- ADD [EBX+8], EAX = 01 43 08
#eval encode 0 (Instr.BOP OpSize.Op32 BinOp.ADD
                (DstSrc.MR (MemSpec.regDisp EBX 8) EAX))
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

# References

- Kennedy, Benton, Jensen, Dagand. "Coq: The World's Best Macro Assembler?" PPDP 2013
- Intel 64 and IA-32 Architectures Software Developer's Manual
- x86proved: https://github.com/msr-quarc/x86proved

