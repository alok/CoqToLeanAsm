/-
  X86Docs/Macros.lean - Documentation for control flow macros
-/

import VersoManual
import CoqToLeanAsm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open X86

set_option pp.rawOnError true

#doc (Manual) "Control Flow Macros" =>

One of the key contributions of the original paper is demonstrating how
to build high-level control flow constructs as "macros" that expand to
sequences of x86 instructions.

# The ProgBuilder Monad

Programs are built using the {lean}`ProgBuilder` monad, which threads
a label generator and accumulates program items:

```lean
structure ProgBuilder (α : Type) where
  run : LabelGen → (α × Program × LabelGen)
```

Key operations:

```lean
-- Emit an instruction
def emit (i : Instr) : ProgBuilder Unit

-- Create a label at the current position
def label (name : String) : ProgBuilder Unit

-- Generate a fresh unique label
def freshLabel : ProgBuilder String
```

# If-Then-Else

The {lean}`ifThenElse` macro generates conditional branches:

```lean
def ifThenElse (cc : Condition) (cv : Bool)
    (pthen pelse : ProgBuilder Unit) : ProgBuilder Unit
```

This expands to:
```
    JCC !cc !cv ELSE
    <then branch>
    JMP END
ELSE:
    <else branch>
END:
```

Example usage:

```lean
-- If ZF is set, do the "then" branch
ifThenElse .Z true
  (ProgBuilder.emit (.MOVOP .Op32 (.RI EAX 1)))
  (ProgBuilder.emit (.MOVOP .Op32 (.RI EAX 0)))
```

# While Loops

The {lean}`while` macro generates pre-test loops:

```lean
def «while» (ptest : ProgBuilder Unit) (cc : Condition) (cv : Bool)
    (pbody : ProgBuilder Unit) : ProgBuilder Unit
```

This expands to:
```
    JMP TEST
BODY:
    <body>
TEST:
    <test>
    JCC cc cv BODY
```

Example:

```lean
-- while (ECX != 0) { EAX *= ECX; ECX-- }
X86.«while»
  (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
  .Z false  -- continue while NOT zero
  (do
    ProgBuilder.emit (.IMUL EAX (.R ECX))
    ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))
```

# Do-While Loops

The {lean}`doWhile` macro generates post-test loops:

```lean
def doWhile (pbody : ProgBuilder Unit) (ptest : ProgBuilder Unit)
    (cc : Condition) (cv : Bool) : ProgBuilder Unit
```

This expands to:
```
BODY:
    <body>
    <test>
    JCC cc cv BODY
```

# For Loops

A countdown for loop:

```lean
def forLoop (counter : Reg) (count : DWord)
    (pbody : ProgBuilder Unit) : ProgBuilder Unit
```

This expands to:
```
    MOV counter, count
    TEST counter, counter
    JZ END
LOOP:
    <body>
    DEC counter
    JNZ LOOP
END:
```

# Procedures

Standard procedure prologue and epilogue:

```lean
def proc (name : String) (localBytes : Nat := 0)
    (body : ProgBuilder Unit) : ProgBuilder Unit
```

This generates:
```
name:
    PUSH EBP
    MOV EBP, ESP
    SUB ESP, localBytes  ; if localBytes > 0
    <body>
    MOV ESP, EBP
    POP EBP
    RET
```

# Building Programs

To convert a {lean}`ProgBuilder` to a {lean}`Program`:

```lean
def buildProg (m : ProgBuilder Unit) : Program :=
  (m.build).2
```

The result can then be assembled:

```lean
let prog := ProgBuilder.buildProg do
  ProgBuilder.emit (.BOP .Op32 .XOR (.RR EAX EAX))
  -- ... more instructions

match assemble 0x1000 prog with
| .ok bytes => IO.println (hexDump bytes 0x1000)
| .error errs => IO.println s!"Errors: {repr errs}"
```
