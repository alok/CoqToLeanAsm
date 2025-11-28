/-
  Macros.lean - Assembly macros for control flow

  This module provides high-level control flow constructs as
  "macros" that expand to sequences of x86 instructions,
  matching the Coq macros.v from x86proved.

  Includes:
  - Lexically scoped labels
  - If-then-else
  - While loops
  - Procedure calls
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Syntax

namespace X86

-- Fresh label generation
structure LabelGen where
  counter : Nat
deriving Inhabited

namespace LabelGen

def fresh (lg : LabelGen) (labelPrefix : String := "L") : String × LabelGen :=
  (s!"{labelPrefix}{lg.counter}", { counter := lg.counter + 1 })

def freshN (lg : LabelGen) (n : Nat) (labelPrefix : String := "L") : List String × LabelGen :=
  let rec go (i : Nat) (lg : LabelGen) (acc : List String) : List String × LabelGen :=
    if i >= n then (acc.reverse, lg)
    else
      let (l, lg') := lg.fresh labelPrefix
      go (i + 1) lg' (l :: acc)
  go 0 lg []

end LabelGen

-- Program builder monad
structure ProgBuilder (α : Type) where
  run : LabelGen → (α × Program × LabelGen)

namespace ProgBuilder

def pure (a : α) : ProgBuilder α := ⟨fun lg => (a, [], lg)⟩

def bind (m : ProgBuilder α) (f : α → ProgBuilder β) : ProgBuilder β :=
  ⟨fun lg =>
    let (a, p1, lg') := m.run lg
    let (b, p2, lg'') := (f a).run lg'
    (b, p1 ++ p2, lg'')⟩

instance : Monad ProgBuilder where
  pure := pure
  bind := bind

-- Emit an instruction
def emit (i : Instr) : ProgBuilder Unit :=
  ⟨fun lg => ((), [.Instr i], lg)⟩

-- Emit a program
def emitProg (p : Program) : ProgBuilder Unit :=
  ⟨fun lg => ((), p, lg)⟩

-- Emit a label
def label (name : String) : ProgBuilder Unit :=
  ⟨fun lg => ((), [.Label name], lg)⟩

-- Emit data bytes
def data (bs : List Byte) : ProgBuilder Unit :=
  ⟨fun lg => ((), [.Data bs], lg)⟩

-- Generate a fresh label
def freshLabel (labelPrefix : String := "L") : ProgBuilder String :=
  ⟨fun lg =>
    let (l, lg') := lg.fresh labelPrefix
    (l, [], lg')⟩

-- Execute the builder
def build (m : ProgBuilder α) (startCounter : Nat := 0) : α × Program :=
  let (a, p, _) := m.run { counter := startCounter }
  (a, p)

def buildProg (m : ProgBuilder Unit) (startCounter : Nat := 0) : Program :=
  (m.build startCounter).2

end ProgBuilder

-- Local scope for labels (using builder monad)
def LOCAL (body : String → ProgBuilder Unit) : ProgBuilder Unit := do
  let l ← ProgBuilder.freshLabel
  body l

-- Multiple local labels
def LOCAL2 (body : String → String → ProgBuilder Unit) : ProgBuilder Unit := do
  let l1 ← ProgBuilder.freshLabel
  let l2 ← ProgBuilder.freshLabel
  body l1 l2

def LOCAL3 (body : String → String → String → ProgBuilder Unit) : ProgBuilder Unit := do
  let l1 ← ProgBuilder.freshLabel
  let l2 ← ProgBuilder.freshLabel
  let l3 ← ProgBuilder.freshLabel
  body l1 l2 l3

-- Convert condition to jump instruction (placeholder target)
def condToJCC (cc : Condition) (cv : Bool) (target : DWord) : Instr :=
  .JCCrel cc cv ⟨target⟩

-- If-then-else macro
-- if (cc, cv) then pthen else pelse
-- Generates:
--   JCC !cc !cv ELSE
--   pthen
--   JMP END
-- ELSE:
--   pelse
-- END:
def ifThenElse (cc : Condition) (cv : Bool)
    (pthen pelse : ProgBuilder Unit) : ProgBuilder Unit := do
  LOCAL2 fun labelElse labelEnd => do
    -- Jump to else if condition is NOT met
    ProgBuilder.emit (.JCCrel cc (!cv) ⟨0⟩)  -- Placeholder, resolved by assembler
    pthen
    ProgBuilder.emit (.JMPrel (.I ⟨0⟩))  -- Placeholder
    ProgBuilder.label labelElse
    pelse
    ProgBuilder.label labelEnd

-- If-then (no else branch)
def ifThen (cc : Condition) (cv : Bool) (pthen : ProgBuilder Unit) : ProgBuilder Unit := do
  LOCAL fun labelEnd => do
    ProgBuilder.emit (.JCCrel cc (!cv) ⟨0⟩)
    pthen
    ProgBuilder.label labelEnd

-- While loop macro
-- while (test; cc cv) body
-- Generates:
--   JMP TEST
-- BODY:
--   body
-- TEST:
--   test
--   JCC cc cv BODY
def «while» (ptest : ProgBuilder Unit) (cc : Condition) (cv : Bool)
    (pbody : ProgBuilder Unit) : ProgBuilder Unit := do
  LOCAL2 fun labelBody labelTest => do
    ProgBuilder.emit (.JMPrel (.I ⟨0⟩))  -- Jump to test
    ProgBuilder.label labelBody
    pbody
    ProgBuilder.label labelTest
    ptest
    ProgBuilder.emit (.JCCrel cc cv ⟨0⟩)  -- Jump to body if condition met

-- Do-while loop
-- do body while (test; cc cv)
-- Generates:
-- BODY:
--   body
--   test
--   JCC cc cv BODY
def doWhile (pbody : ProgBuilder Unit) (ptest : ProgBuilder Unit)
    (cc : Condition) (cv : Bool) : ProgBuilder Unit := do
  LOCAL fun labelBody => do
    ProgBuilder.label labelBody
    pbody
    ptest
    ProgBuilder.emit (.JCCrel cc cv ⟨0⟩)

-- For loop (countdown from n to 0)
-- for ECX = n downto 0 do body
-- Generates:
--   MOV ECX, n
--   TEST ECX, ECX
--   JZ END
-- LOOP:
--   body
--   DEC ECX
--   JNZ LOOP
-- END:
def forLoop (counter : Reg) (count : DWord) (pbody : ProgBuilder Unit) : ProgBuilder Unit := do
  LOCAL2 fun labelLoop labelEnd => do
    ProgBuilder.emit (.MOVOP .Op32 (.RI counter count))
    ProgBuilder.emit (.TESTOP .Op32 (.R counter) (.R counter))
    ProgBuilder.emit (.JCCrel .Z true ⟨0⟩)  -- JZ END
    ProgBuilder.label labelLoop
    pbody
    ProgBuilder.emit (.UOP .Op32 .DEC (.R counter))
    ProgBuilder.emit (.JCCrel .Z false ⟨0⟩)  -- JNZ LOOP
    ProgBuilder.label labelEnd

-- Simple conditional jumps (sugar)
def JZ (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .Z true ⟨0⟩)

def JNZ (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .Z false ⟨0⟩)

def JA (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .BE false ⟨0⟩)

def JB (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .B true ⟨0⟩)

def JAE (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .B false ⟨0⟩)

def JBE (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .BE true ⟨0⟩)

def JG (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .LE false ⟨0⟩)

def JL (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .L true ⟨0⟩)

def JGE (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .L false ⟨0⟩)

def JLE (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.JCCrel .LE true ⟨0⟩)

-- Procedure prologue/epilogue
-- Standard calling convention setup
def procPrologue (localBytes : Nat := 0) : ProgBuilder Unit := do
  ProgBuilder.emit (.PUSH (.R EBP))
  ProgBuilder.emit (.MOVOP .Op32 (.RR EBP ESP))
  if localBytes > 0 then
    ProgBuilder.emit (.BOP .Op32 .SUB (.RI ESP (BitVec.ofNat 32 localBytes)))

def procEpilogue : ProgBuilder Unit := do
  ProgBuilder.emit (.MOVOP .Op32 (.RR ESP EBP))
  ProgBuilder.emit (.POP (.R EBP))
  ProgBuilder.emit (.RETOP 0)

-- Define a procedure
def proc (name : String) (localBytes : Nat := 0) (body : ProgBuilder Unit) : ProgBuilder Unit := do
  ProgBuilder.label name
  procPrologue localBytes
  body
  procEpilogue

-- Call a procedure (by label, resolved later)
-- Note: Named callProc to avoid conflict with x86! syntax keyword
def callProc (target : String) : ProgBuilder Unit :=
  ProgBuilder.emit (.CALLrel (.I ⟨0⟩))

-- Stack operations with expressions
def pushAll (regs : List Reg) : ProgBuilder Unit :=
  regs.forM fun r => ProgBuilder.emit (.PUSH (.R r))

def popAll (regs : List Reg) : ProgBuilder Unit :=
  regs.reverse.forM fun r => ProgBuilder.emit (.POP (.R r))

-- Save and restore caller-save registers around a call
def saveCallerRegs : ProgBuilder Unit := pushAll [EAX, ECX, EDX]
def restoreCallerRegs : ProgBuilder Unit := popAll [EAX, ECX, EDX]

-- Switch/case macro (on EAX)
-- switch EAX { 0 => p0, 1 => p1, ... }
def switch (cases : List (Nat × ProgBuilder Unit)) (default : ProgBuilder Unit) :
    ProgBuilder Unit := do
  LOCAL fun labelEnd => do
    for (val, prog) in cases do
      LOCAL fun labelNext => do
        ProgBuilder.emit (.BOP .Op32 .CMP (.RI EAX (BitVec.ofNat 32 val)))
        ProgBuilder.emit (.JCCrel .Z false ⟨0⟩)  -- JNE next
        prog
        ProgBuilder.emit (.JMPrel (.I ⟨0⟩))  -- JMP end
        ProgBuilder.label labelNext
    default
    ProgBuilder.label labelEnd

-- Memory copy: copy ECX bytes from ESI to EDI
-- Uses: rep movsb semantics (simplified)
def memcpy : ProgBuilder Unit := do
  LOCAL fun labelLoop => do
    ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX))
    ProgBuilder.emit (.JCCrel .Z true ⟨0⟩)  -- JZ end (ECX=0)
    ProgBuilder.label labelLoop
    -- MOV AL, [ESI]
    ProgBuilder.emit (.MOVOP .Op8 (.RM AL (MemSpec.reg ESI)))
    -- MOV [EDI], AL
    ProgBuilder.emit (.MOVOP .Op8 (.MR (MemSpec.reg EDI) AL))
    -- INC ESI, INC EDI, DEC ECX
    ProgBuilder.emit (.UOP .Op32 .INC (.R ESI))
    ProgBuilder.emit (.UOP .Op32 .INC (.R EDI))
    ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX))
    ProgBuilder.emit (.JCCrel .Z false ⟨0⟩)  -- JNZ loop

-- Memory set: set ECX bytes at EDI to AL
def memset : ProgBuilder Unit := do
  LOCAL2 fun labelLoop labelEnd => do
    ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX))
    ProgBuilder.emit (.JCCrel .Z true ⟨0⟩)
    ProgBuilder.label labelLoop
    ProgBuilder.emit (.MOVOP .Op8 (.MR (MemSpec.reg EDI) AL))
    ProgBuilder.emit (.UOP .Op32 .INC (.R EDI))
    ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX))
    ProgBuilder.emit (.JCCrel .Z false ⟨0⟩)
    ProgBuilder.label labelEnd

-- String length (null-terminated string at EDI, result in EAX)
def strlen : ProgBuilder Unit := do
  LOCAL2 fun labelLoop labelEnd => do
    ProgBuilder.emit (.BOP .Op32 .XOR (.RR EAX EAX))  -- EAX = 0
    ProgBuilder.label labelLoop
    ProgBuilder.emit (.MOVOP .Op8 (.RM AL (MemSpec.reg EDI)))
    ProgBuilder.emit (.TESTOP .Op8 (.R AL) (.R AL))
    ProgBuilder.emit (.JCCrel .Z true ⟨0⟩)  -- JZ end
    ProgBuilder.emit (.UOP .Op32 .INC (.R EDI))
    ProgBuilder.emit (.UOP .Op32 .INC (.R EAX))
    ProgBuilder.emit (.JMPrel (.I ⟨0⟩))  -- JMP loop
    ProgBuilder.label labelEnd

end X86
