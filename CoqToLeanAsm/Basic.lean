/-
  CoqToLeanAsm - x86 Macro Assembler in Lean 4

  A port of "Coq: The World's Best Macro Assembler?" to Lean 4.
  Original paper by Kennedy, Benton, Jensen, and Dagand (PPDP 2013).

  This library provides:
  - Concrete bit/byte representations (using Lean's BitVec)
  - x86-32 instruction set encoding
  - Intel assembly syntax via Lean macros
  - Separation logic for program verification
  - Multi-pass assembler with label resolution
  - Control flow macros (if-then-else, while, procedures)

  Key modules:
  - Bits.lean: Bit vector operations
  - Reg.lean: x86 registers
  - Instr.lean: Instruction definitions
  - Mem.lean: Memory model and processor state
  - Encode.lean: Instruction encoding
  - Syntax.lean: Assembly syntax macros
  - SepLogic.lean: Separation logic predicates
  - Assembler.lean: Multi-pass assembler
  - Macros.lean: Control flow constructs
  - Examples.lean: Example programs
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Mem
import CoqToLeanAsm.Encode
import CoqToLeanAsm.Syntax
import CoqToLeanAsm.SepLogic
import CoqToLeanAsm.Assembler
import CoqToLeanAsm.Macros
import CoqToLeanAsm.Examples

namespace X86

/-!
# Quick Start

## Writing Assembly

Use the `asm!` macro for Intel-style syntax:

```lean
-- Single instruction
#check asm! MOV EAX, EBX

-- Program
def myProg := asm! {
  MOV EAX, 0;;
  ADD EAX, [EBX + 4];;
  RET
}
```

## Memory Addressing

Supported addressing modes:
- `[EAX]` - Register indirect
- `[EAX + 4]` - Register + displacement
- `[EAX + EBX*4]` - Scaled index
- `[EAX + EBX*4 + 8]` - Full SIB addressing
- `[0x12345678]` - Absolute address

## Control Flow Macros

```lean
open ProgBuilder in
def myFunc := buildProg do
  -- If-then-else
  emit (.TESTOP .Op32 (.R EAX) (.R EAX))
  ifThenElse .Z true
    (emit (.MOVOP .Op32 (.RI EBX 1)))  -- then
    (emit (.MOVOP .Op32 (.RI EBX 0)))  -- else

  -- While loop
  while
    (emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
    .Z false
    (do
      emit (.UOP .Op32 .DEC (.R ECX)))

  -- Procedure
  proc "myProc" 16 do
    -- local stack frame of 16 bytes
    emit .NOP
```

## Assembly

```lean
match assemble 0x1000 myProg with
| .ok bytes => IO.println (hexDump bytes 0x1000)
| .error errs => IO.println s!"Errors: {repr errs}"
```

## Verification with Separation Logic

```lean
-- Register assertion
#check (EAX ~= 42 : SPred)

-- Memory assertion
#check ((0x1000 : DWord) :-> (0x42 : Byte) : SPred)

-- Separating conjunction
#check (EAX ~= 42 ** EBX ~= 0 : SPred)
```
-/

end X86
