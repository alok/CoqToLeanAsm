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

The assembler provides:

- *Bit-precise types* using Lean 4's {lean}`BitVec` for bytes, words, and double words
- *Full x86-32 register model* including general-purpose, byte, and segment registers
- *Comprehensive instruction encoding* with ModR/M and SIB byte generation
- *Separation logic predicates* for reasoning about memory and registers
- *Multi-pass assembler* with label resolution
- *Control flow macros* (if-then-else, while loops, procedures)

# Quick Start

Here's a simple example encoding some x86 instructions:

```lean
-- Basic instructions encode to their expected bytes
#eval encode 0 Instr.NOP        -- [0x90]
#eval encode 0 (Instr.RETOP 0)  -- [0xC3]
#eval encode 0 Instr.HLT        -- [0xF4]
```

# Module Structure

The codebase is organized into the following modules:

| Module | Description |
|--------|-------------|
| `CoqToLeanAsm.Bits` | Byte, Word, DWord types and hex conversion |
| `CoqToLeanAsm.Reg` | x86 register definitions |
| `CoqToLeanAsm.Instr` | Instruction ADT with addressing modes |
| `CoqToLeanAsm.Mem` | Memory model and processor state |
| `CoqToLeanAsm.Encode` | Instruction encoding to bytes |
| `CoqToLeanAsm.SepLogic` | Separation logic predicates |
| `CoqToLeanAsm.Macros` | Control flow constructs |
| `CoqToLeanAsm.Assembler` | Multi-pass assembler |

# Registers

The x86-32 architecture provides several register types.

## General Purpose Registers

The eight 32-bit general purpose registers are defined by the {lean}`Reg` type:

```lean
#check EAX
#check ECX
#check EDX
#check EBX
```

Each register has an associated encoding (0-7) used in ModR/M bytes.

## Byte Registers

The 8-bit byte registers provide access to the low bytes:

```lean
#check AL
#check AH
```

# Instructions

The x86 instruction set is represented by the {lean}`Instr` type.

## Operand Sizes

Instructions operate on 8-bit or 32-bit operands:

```lean
#check OpSize.Op8
#check OpSize.Op32
```

## Memory Addressing

x86 supports complex memory addressing modes via {lean}`MemSpec`:

```lean
-- [EBX]
#check MemSpec.reg EBX

-- [EBX + 4]
#check MemSpec.regDisp EBX 4

-- [0x12345678]
#check MemSpec.disp 0x12345678
```

## Data Movement

```lean
-- MOV EAX, 42
#check Instr.MOVOP OpSize.Op32 (DstSrc.RI EAX 42)

-- PUSH EAX
#check Instr.PUSH (Src.R EAX)

-- POP EBX
#check Instr.POP (RegMem.R EBX)
```

## Arithmetic Operations

```lean
-- ADD EAX, EBX
#check Instr.BOP OpSize.Op32 BinOp.ADD (DstSrc.RR EAX EBX)

-- SUB EAX, 10
#check Instr.BOP OpSize.Op32 BinOp.SUB (DstSrc.RI EAX 10)

-- INC ECX
#check Instr.UOP OpSize.Op32 UnaryOp.INC (RegMem.R ECX)
```

# Encoding

x86 instruction encoding involves opcodes, ModR/M bytes, SIB bytes, and immediates.

## ModR/M Byte

The ModR/M byte specifies addressing modes:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
|  mod  |   reg/op  |    r/m    |
+---+---+---+---+---+---+---+---+
```

## Encoding Examples

```lean
-- NOP = 0x90
#eval encode 0 Instr.NOP

-- RET = 0xC3
#eval encode 0 (Instr.RETOP 0)

-- MOV EAX, EBX = 89 D8
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RR EAX EBX))

-- MOV EAX, 42 = B8 2A 00 00 00
#eval encode 0 (Instr.MOVOP OpSize.Op32 (DstSrc.RI EAX 42))
```

# Control Flow Macros

High-level control flow constructs expand to instruction sequences.

## The ProgBuilder Monad

Programs are built using {lean}`ProgBuilder`:

```lean
#check ProgBuilder
#check ProgBuilder.emit
#check ProgBuilder.label
```

## If-Then-Else

```lean
#check ifThenElse
#check ifThen
```

## While Loops

```lean
#check X86.«while»
#check doWhile
```

## Procedures

```lean
#check proc
#check procPrologue
#check procEpilogue
```

# Examples

## Factorial

Computes n! for input n in ECX, result in EAX:

```lean
def factorialExample : Program := ProgBuilder.buildProg do
  ProgBuilder.emit (Instr.MOVOP OpSize.Op32 (DstSrc.RI EAX 1))
  X86.«while»
    (ProgBuilder.emit (Instr.TESTOP OpSize.Op32 (RegMem.R ECX) (RegImm.R ECX)))
    Condition.Z false
    (do
      ProgBuilder.emit (Instr.IMUL EAX (RegMem.R ECX))
      ProgBuilder.emit (Instr.UOP OpSize.Op32 UnaryOp.DEC (RegMem.R ECX)))
```

## Assembly Output

```lean
#eval! do
  match assemble 0x1000 factorialExample with
  | .ok bytes => IO.println s!"Assembled {bytes.length} bytes"
  | .error _ => IO.println "Assembly failed"
```
