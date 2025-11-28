/-
  X86Docs/Registers.lean - Documentation for x86 registers
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open X86

set_option pp.rawOnError true

#doc (Manual) "Registers" =>

The x86-32 architecture provides several register types. This module defines
type-safe representations for all of them.

# General Purpose Registers

The eight 32-bit general purpose registers are defined by the {lean}`Reg` type:

```lean
inductive Reg where
  | EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI
```

Each register has an associated encoding (0-7) used in ModR/M bytes:

```lean
#eval Reg.regEnc EAX  -- 0
#eval Reg.regEnc ECX  -- 1
#eval Reg.regEnc EDX  -- 2
#eval Reg.regEnc EBX  -- 3
```

# Byte Registers

The 8-bit byte registers provide access to the low bytes of the first four
general purpose registers:

```lean
inductive ByteReg where
  | AL | CL | DL | BL | AH | CH | DH | BH
```

Note that {lean}`AL`, {lean}`CL`, {lean}`DL`, {lean}`BL` access the low byte,
while {lean}`AH`, {lean}`CH`, {lean}`DH`, {lean}`BH` access the high byte
of the 16-bit portion.

# Non-Stack-Pointer Registers

For certain instructions that cannot use ESP as a base register, we use
{lean}`NonSPReg`:

```lean
inductive NonSPReg where
  | EAX | ECX | EDX | EBX | EBP | ESI | EDI
```

This is used in the SIB byte index field where ESP is interpreted specially.

# Segment Registers

Segment registers are rarely used in modern 32-bit protected mode code,
but are included for completeness:

```lean
inductive SegReg where
  | ES | CS | SS | DS | FS | GS
```

# Unified Register Access

The {lean}`AnyReg` type provides a unified view over all register sizes:

```lean
inductive AnyReg where
  | R32 : Reg → AnyReg
  | R16 : Reg → AnyReg
  | R8  : ByteReg → AnyReg
```
