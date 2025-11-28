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

- **Bit-precise types** using Lean 4's {lean}`BitVec` for bytes, words, and double words
- **Full x86-32 register model** including general-purpose, byte, and segment registers
- **Comprehensive instruction encoding** with ModR/M and SIB byte generation
- **Separation logic predicates** for reasoning about memory and registers
- **Multi-pass assembler** with label resolution
- **Control flow macros** (if-then-else, while loops, procedures)

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
| {lean}`CoqToLeanAsm.Bits` | Byte, Word, DWord types and hex conversion |
| {lean}`CoqToLeanAsm.Reg` | x86 register definitions |
| {lean}`CoqToLeanAsm.Instr` | Instruction ADT with addressing modes |
| {lean}`CoqToLeanAsm.Mem` | Memory model and processor state |
| {lean}`CoqToLeanAsm.Encode` | Instruction encoding to bytes |
| {lean}`CoqToLeanAsm.SepLogic` | Separation logic predicates |
| {lean}`CoqToLeanAsm.Macros` | Control flow constructs |
| {lean}`CoqToLeanAsm.Assembler` | Multi-pass assembler |

{include 0 X86Docs.Registers}
{include 0 X86Docs.Instructions}
{include 0 X86Docs.Encoding}
{include 0 X86Docs.Macros}
{include 0 X86Docs.Examples}
