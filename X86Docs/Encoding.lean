/-
  X86Docs/Encoding.lean - Documentation for instruction encoding
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open X86

set_option pp.rawOnError true

#doc (Manual) "Encoding" =>

x86 instruction encoding is complex, involving opcodes, ModR/M bytes,
SIB bytes, and immediate values. This module handles all the details.

# The ByteWriter Monad

Encoding is done using the {lean}`ByteWriter` monad, which accumulates
bytes:

```lean
structure ByteWriter (α : Type) where
  run : List Byte → α × List Byte
```

Operations include:

```lean
-- Emit a single byte
def emitByte (b : Byte) : ByteWriter Unit

-- Emit a word (2 bytes, little-endian)
def emitWord (w : Word) : ByteWriter Unit

-- Emit a double word (4 bytes, little-endian)
def emitDWord (d : DWord) : ByteWriter Unit
```

# ModR/M Byte

The ModR/M byte specifies addressing modes:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
|  mod  |   reg/op  |    r/m    |
+---+---+---+---+---+---+---+---+
```

- **mod**: Addressing mode (00=no disp, 01=disp8, 10=disp32, 11=register)
- **reg/op**: Register operand or opcode extension
- **r/m**: Register or memory operand

```lean
def mkModRM (mod : Nat) (regop : Nat) (rm : Nat) : Byte :=
  BitVec.ofNat 8 ((mod <<< 6) ||| (regop <<< 3) ||| rm)
```

# SIB Byte

When r/m = 4 (ESP encoding) and mod ≠ 11, a SIB byte follows:

```
 7   6   5   4   3   2   1   0
+---+---+---+---+---+---+---+---+
| scale |   index   |   base    |
+---+---+---+---+---+---+---+---+
```

- **scale**: 00=×1, 01=×2, 10=×4, 11=×8
- **index**: Index register (ESP means no index)
- **base**: Base register

# Encoding Examples

Simple instructions have fixed encodings:

```lean
#eval encode 0 .NOP  -- [0x90]

#eval encode 0 .HLT  -- [0xF4]

#eval encode 0 (.RETOP 0)  -- [0xC3]
```

Register-to-register MOV uses ModR/M:

```lean
-- MOV EAX, EBX encodes as 89 D8
-- Opcode 89 = MOV r/m32, r32
-- ModR/M D8 = 11 011 000 = mod=11 (reg), reg=EBX(3), r/m=EAX(0)
#eval encode 0 (.MOVOP .Op32 (.RR EAX EBX))  -- [0x89, 0xD8]
```

Memory addressing with displacement:

```lean
-- MOV EAX, [EBX+4] encodes as 8B 43 04
-- Opcode 8B = MOV r32, r/m32
-- ModR/M 43 = 01 000 011 = mod=01 (disp8), reg=EAX(0), r/m=EBX(3)
-- Displacement: 04
#eval encode 0 (.MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBX 4)))
-- [0x8B, 0x43, 0x04]
```

Immediate operands:

```lean
-- MOV EAX, 0x12345678 encodes as B8 78 56 34 12
-- Opcode B8+r = MOV r32, imm32 (B8 = EAX)
-- Little-endian immediate follows
#eval encode 0 (.MOVOP .Op32 (.RI EAX 0x12345678))
-- [0xB8, 0x78, 0x56, 0x34, 0x12]
```

# Little-Endian Byte Order

x86 uses little-endian byte order for multi-byte values:

```lean
-- The value 0x12345678 is stored as: 78 56 34 12
def dwordToBytes (d : DWord) : List Byte :=
  [ d.truncate 8,
    (d >>> 8).truncate 8,
    (d >>> 16).truncate 8,
    (d >>> 24).truncate 8 ]
```
