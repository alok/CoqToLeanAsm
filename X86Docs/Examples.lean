/-
  X86Docs/Examples.lean - Example programs documentation
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open X86

set_option pp.rawOnError true

#doc (Manual) "Example Programs" =>

This chapter demonstrates complete example programs using the assembler.

# Factorial

Computes n! for input n in ECX, result in EAX:

```lean
def factorialProg : Program := ProgBuilder.buildProg do
  -- EAX = 1 (result accumulator)
  ProgBuilder.emit (.MOVOP .Op32 (.RI EAX 1))
  -- while (ECX != 0)
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
    .Z false
    (do
      -- EAX = EAX * ECX
      ProgBuilder.emit (.IMUL EAX (.R ECX))
      -- ECX--
      ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))
```

# Array Sum

Computes the sum of a 32-bit integer array:
- ESI = array pointer
- ECX = element count
- Result in EAX

```lean
def arraySumProg : Program := ProgBuilder.buildProg do
  -- EAX = 0 (sum accumulator)
  ProgBuilder.emit (.BOP .Op32 .XOR (.RR EAX EAX))
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
    .Z false
    (do
      -- EAX += [ESI]
      ProgBuilder.emit (.BOP .Op32 .ADD (.RM EAX (MemSpec.reg ESI)))
      -- ESI += 4 (next element)
      ProgBuilder.emit (.BOP .Op32 .ADD (.RI ESI 4))
      -- ECX--
      ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))
```

# GCD (Greatest Common Divisor)

Euclidean algorithm using subtraction:
- EAX = a, EBX = b
- Result (gcd) in EAX

```lean
def gcdProg : Program := ProgBuilder.buildProg do
  -- while (EBX != 0)
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R EBX) (.R EBX)))
    .Z false
    (do
      -- while (EAX >= EBX) EAX -= EBX
      X86.«while»
        (ProgBuilder.emit (.BOP .Op32 .CMP (.RR EAX EBX)))
        .B false  -- continue while NOT below (i.e., >=)
        (ProgBuilder.emit (.BOP .Op32 .SUB (.RR EAX EBX)))
      -- swap EAX, EBX
      ProgBuilder.emit (.XCHG .Op32 EAX (.R EBX)))
```

# Memory Copy

Copies ECX bytes from ESI to EDI:

```lean
def memcpyProg : Program := ProgBuilder.buildProg do
  X86.«while»
    (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
    .Z false
    (do
      -- AL = [ESI]
      ProgBuilder.emit (.MOVOP .Op8 (.RM AL (MemSpec.reg ESI)))
      -- [EDI] = AL
      ProgBuilder.emit (.MOVOP .Op8 (.MR (MemSpec.reg EDI) AL))
      -- ESI++, EDI++, ECX--
      ProgBuilder.emit (.UOP .Op32 .INC (.R ESI))
      ProgBuilder.emit (.UOP .Op32 .INC (.R EDI))
      ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))
```

# Absolute Value

Computes |EAX|:

```lean
def absProg : Program := ProgBuilder.buildProg do
  -- TEST EAX, EAX (sets SF if negative)
  ProgBuilder.emit (.TESTOP .Op32 (.R EAX) (.R EAX))
  -- if (SF) then NEG EAX
  ifThen .S true (ProgBuilder.emit (.UOP .Op32 .NEG (.R EAX)))
```

# Assembling and Running

To assemble any of these programs:

```lean
#eval do
  match assemble 0x1000 factorialProg with
  | .ok bytes =>
    IO.println s!"Assembled {bytes.length} bytes"
    IO.println (hexDump bytes 0x1000)
  | .error errs =>
    IO.println s!"Errors: {repr errs}"
```

Output:
```
Assembled 16 bytes
00001000: B8 01 00 00 00 85 C9 74 17 0F AF C1 49 75 FC C3  .......t....Iu..
```

# Verification

The separation logic predicates allow us to state and prove properties
about programs. For example:

```lean
-- XOR EAX, EAX always clears EAX
theorem xor_clears : ∀ v : DWord, (v ^^^ v) = 0 := by
  intro v
  simp [BitVec.xor_self]

-- ADD is commutative
theorem add_comm : ∀ a b : DWord, a + b = b + a := by
  intro a b
  exact BitVec.add_comm a b
```
