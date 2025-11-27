/-
  SepLogic.lean - Separation Logic Predicates

  This module defines separation logic predicates for reasoning about
  memory and state, matching the Coq pointsto.v from x86proved.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Mem

namespace X86

-- Separation logic predicate (assertion about state)
def SPred := ProcState → Prop

namespace SPred

-- True (always holds)
def emp : SPred := fun _ => True

-- False (never holds)
def «false» : SPred := fun _ => False

-- Pure assertion (lift a Prop to SPred)
def pure (P : Prop) : SPred := fun _ => P

-- Conjunction
def and (P Q : SPred) : SPred := fun s => P s ∧ Q s

-- Disjunction
def or (P Q : SPred) : SPred := fun s => P s ∨ Q s

-- Implication
def imp (P Q : SPred) : SPred := fun s => P s → Q s

-- Existential
def ex (P : α → SPred) : SPred := fun s => ∃ a, P a s

-- Universal
def all (P : α → SPred) : SPred := fun s => ∀ a, P a s

-- Negation
def not (P : SPred) : SPred := fun s => ¬P s

-- Entailment
def entails (P Q : SPred) : Prop := ∀ s, P s → Q s

-- Bi-entailment (logical equivalence)
def equiv (P Q : SPred) : Prop := entails P Q ∧ entails Q P

end SPred

-- Notation
scoped infixr:35 " ∧∧ " => SPred.and
scoped infixr:30 " ∨∨ " => SPred.or
scoped infixr:25 " →→ " => SPred.imp
scoped notation:max "∃∃ " x ", " P => SPred.ex (fun x => P)
scoped notation:max "∀∀ " x ", " P => SPred.all (fun x => P)
scoped infixl:20 " |-- " => SPred.entails
scoped infixl:20 " -|- " => SPred.equiv

-- Separating conjunction (simplified)
def sep (P Q : SPred) : SPred := fun s => P s ∧ Q s

scoped infixr:40 " ** " => sep

-- Magic wand (simplified)
def wand (P Q : SPred) : SPred := fun s =>
  ∀ s', P s' → Q s'

scoped infixr:25 " -* " => wand

-- Byte points-to
def byteIs (p : DWord) (b : Byte) : SPred := fun s =>
  s.mem.readByte p = b

-- Word points-to (little-endian)
def wordIs (p : DWord) (w : Word) : SPred := fun s =>
  s.mem.readByte p = w.toByte ⟨0, by omega⟩ ∧
  s.mem.readByte (p + 1) = w.toByte ⟨1, by omega⟩

-- DWord points-to (little-endian)
def dwordIs (p : DWord) (d : DWord) : SPred := fun s =>
  s.mem.readByte p = d.toByte ⟨0, by omega⟩ ∧
  s.mem.readByte (p + 1) = d.toByte ⟨1, by omega⟩ ∧
  s.mem.readByte (p + 2) = d.toByte ⟨2, by omega⟩ ∧
  s.mem.readByte (p + 3) = d.toByte ⟨3, by omega⟩

-- Notation for points-to
scoped notation:50 p " :->b " v => byteIs p v
scoped notation:50 p " :->w " v => wordIs p v
scoped notation:50 p " :->d " v => dwordIs p v

-- Register assertion
def regIs (r : Reg) (v : DWord) : SPred := fun s =>
  s.regs.readReg r = v

scoped notation:50 r " ~= " v => regIs r v

-- Any register assertion
def anyRegIs (r : AnyReg) (v : DWord) : SPred := fun s =>
  s.regs.read r = v

-- EIP assertion
def eipIs (v : DWord) : SPred := anyRegIs .EIP v

-- Flags assertions
def flagIs (getFlag : Flags → Bool) (v : Bool) : SPred := fun s =>
  getFlag s.flags = v

def cfIs := flagIs Flags.CF
def zfIs := flagIs Flags.ZF
def sfIs := flagIs Flags.SF
def ofIs := flagIs Flags.OF

-- Byte sequence in memory
def bytesAt (p : DWord) (bs : List Byte) : SPred := fun s =>
  (bs.zip (List.range bs.length)).all fun (b, i) =>
    s.mem.readByte (p + i.toUInt32.toNat) == b

-- Code at address
def codeAt (p : DWord) (bs : List Byte) : SPred := bytesAt p bs

-- Frame rule helper
def framePreserving (P : SPred) (lo hi : DWord) : Prop :=
  ∀ s s', P s → P s' →
    (∀ addr, addr.toNat < lo.toNat ∨ addr.toNat ≥ hi.toNat →
      s.mem.readByte addr = s'.mem.readByte addr)

-- Basic theorems
theorem emp_and (P : SPred) : SPred.emp ∧∧ P -|- P := by
  constructor
  · intro s ⟨_, hp⟩; exact hp
  · intro s hp; exact ⟨trivial, hp⟩

theorem and_comm (P Q : SPred) : P ∧∧ Q -|- Q ∧∧ P := by
  constructor <;> intro s ⟨hp, hq⟩ <;> exact ⟨hq, hp⟩

theorem sep_comm (P Q : SPred) : P ** Q -|- Q ** P := by
  constructor <;> intro s ⟨hp, hq⟩ <;> exact ⟨hq, hp⟩

theorem sep_assoc (P Q R : SPred) : (P ** Q) ** R -|- P ** (Q ** R) := by
  constructor
  · intro s ⟨⟨hp, hq⟩, hr⟩; exact ⟨hp, hq, hr⟩
  · intro s ⟨hp, hq, hr⟩; exact ⟨⟨hp, hq⟩, hr⟩

theorem ex_sep_comm (P : α → SPred) (Q : SPred) :
    (∃∃ x, P x) ** Q -|- ∃∃ x, (P x ** Q) := by
  constructor
  · intro s ⟨⟨x, hp⟩, hq⟩; exact ⟨x, hp, hq⟩
  · intro s ⟨x, hp, hq⟩; exact ⟨⟨x, hp⟩, hq⟩

-- Register is functional
theorem regIs_functional (r : Reg) (v1 v2 : DWord) :
    (r ~= v1) ∧∧ (r ~= v2) |-- SPred.pure (v1 = v2) := by
  intro s ⟨h1, h2⟩
  simp [regIs] at h1 h2
  exact h1.symm.trans h2

end X86
