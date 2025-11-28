/-
  X86Docs/Instructions.lean - Documentation for x86 instructions
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open X86

set_option pp.rawOnError true

#doc (Manual) "Instructions" =>

The x86 instruction set is represented by the {lean}`Instr` type, which
captures the full variety of x86-32 instructions with their operand modes.

# Operand Sizes

Instructions operate on 8-bit or 32-bit operands, indicated by {lean}`OpSize`:

```lean
inductive OpSize where
  | Op8   -- 8-bit operations
  | Op32  -- 32-bit operations
```

# Memory Addressing

x86 supports complex memory addressing modes. The {lean}`MemSpec` type
captures these:

```lean
-- [reg]
def MemSpec.reg (r : Reg) : MemSpec

-- [reg + disp]
def MemSpec.regDisp (r : Reg) (d : Int) : MemSpec

-- [disp32]
def MemSpec.disp (d : DWord) : MemSpec

-- [base + index*scale]
def MemSpec.regIdx (base : Reg) (idx : NonSPReg) (scale : Scale) : MemSpec

-- [base + index*scale + disp]
def MemSpec.regIdxDisp (base : Reg) (idx : NonSPReg) (scale : Scale) (d : Int) : MemSpec
```

# Instruction Categories

## Data Movement

```lean
-- MOV dst, src
.MOVOP : OpSize → DstSrc s → Instr

-- PUSH src
.PUSH : RegMemImm .Op32 → Instr

-- POP dst
.POP : RegMem .Op32 → Instr

-- XCHG r, r/m
.XCHG : OpSize → Reg → RegMem s → Instr
```

## Arithmetic Operations

Binary operations use {lean}`BinOp`:

```lean
inductive BinOp where
  | ADD | OR | ADC | SBB | AND | SUB | XOR | CMP
```

```lean
-- op dst, src (ADD, SUB, AND, OR, XOR, CMP)
.BOP : OpSize → BinOp → DstSrc s → Instr

-- IMUL r, r/m
.IMUL : Reg → RegMem .Op32 → Instr
```

## Unary Operations

```lean
inductive UnaryOp where
  | INC | DEC | NOT | NEG
```

```lean
-- op r/m (INC, DEC, NOT, NEG)
.UOP : OpSize → UnaryOp → RegMem s → Instr
```

## Shift Operations

```lean
inductive ShiftOp where
  | SHL | SHR | SAL | SAR | ROL | ROR | RCL | RCR
```

```lean
-- shift r/m, count
.SHIFTOP : OpSize → ShiftOp → RegMem s → ShiftCount → Instr
```

## Control Flow

```lean
-- JMP rel32
.JMPrel : RegMemImm .Op32 → Instr

-- Jcc rel8 (conditional jumps)
.JCCrel : Condition → Bool → Tgt → Instr

-- CALL rel32
.CALLrel : RegMemImm .Op32 → Instr

-- RET
.RETOP : Nat → Instr
```

## Flag Operations

```lean
.CLC  -- Clear carry flag
.STC  -- Set carry flag
.CMC  -- Complement carry flag
.CLD  -- Clear direction flag
.STD  -- Set direction flag
```

## Other Instructions

```lean
.NOP  -- No operation
.HLT  -- Halt
.LEA  -- Load effective address
.TESTOP  -- Test (AND without storing result)
```
