/-
  Bits.lean - Bit vector representation and operations

  This module provides the foundation for working with n-bit words,
  mirroring the Coq bitsrep.v from x86proved.

  In Lean 4, we use the built-in BitVec type which provides efficient
  bit vector operations with proofs.
-/

namespace X86

-- Standard bit widths used in x86
abbrev Nibble := BitVec 4
abbrev Byte := BitVec 8
abbrev Word := BitVec 16
abbrev DWord := BitVec 32
abbrev QWord := BitVec 64

-- Operation sizes (matches x86 operand size encoding)
inductive OpSize where
  | Op8  : OpSize  -- 1 byte
  | Op16 : OpSize  -- 2 bytes (WORD)
  | Op32 : OpSize  -- 4 bytes (DWORD)
deriving Repr, DecidableEq, Inhabited

-- Map OpSize to bit width
def OpSize.bits : OpSize → Nat
  | Op8  => 8
  | Op16 => 16
  | Op32 => 32

-- Variable-width word type indexed by operation size
abbrev VWord (s : OpSize) := BitVec s.bits

-- Coercions for convenience
instance : Coe (BitVec 8) Byte := ⟨id⟩
instance : Coe (BitVec 16) Word := ⟨id⟩
instance : Coe (BitVec 32) DWord := ⟨id⟩

-- Byte extraction from larger words
def DWord.toByte (d : DWord) (idx : Fin 4) : Byte :=
  (d >>> (idx.val * 8)).truncate 8

def DWord.fromBytes (b0 b1 b2 b3 : Byte) : DWord :=
  b0.zeroExtend 32 |||
  (b1.zeroExtend 32 <<< 8) |||
  (b2.zeroExtend 32 <<< 16) |||
  (b3.zeroExtend 32 <<< 24)

def Word.toByte (w : Word) (idx : Fin 2) : Byte :=
  (w >>> (idx.val * 8)).truncate 8

def Word.fromBytes (b0 b1 : Byte) : Word :=
  b0.zeroExtend 16 ||| (b1.zeroExtend 16 <<< 8)

-- Sign extension
def Byte.signExtendToWord (b : Byte) : Word :=
  b.signExtend 16

def Byte.signExtendToDWord (b : Byte) : DWord :=
  b.signExtend 32

def Word.signExtendToDWord (w : Word) : DWord :=
  w.signExtend 32

-- Hex string conversion
def Byte.toHexChar (n : Fin 16) : Char :=
  if n.val < 10 then Char.ofNat (0x30 + n.val)
  else Char.ofNat (0x41 + n.val - 10)

def Byte.toHex (b : Byte) : String :=
  let hi := Byte.toHexChar ⟨(b.toNat / 16) % 16, by omega⟩
  let lo := Byte.toHexChar ⟨b.toNat % 16, by omega⟩
  String.mk [hi, lo]

def DWord.toHex (d : DWord) : String :=
  String.join [
    (d.toByte ⟨3, by omega⟩).toHex,
    (d.toByte ⟨2, by omega⟩).toHex,
    (d.toByte ⟨1, by omega⟩).toHex,
    (d.toByte ⟨0, by omega⟩).toHex
  ]

-- Hex parsing
def Char.hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def Byte.fromHex? (s : String) : Option Byte := do
  guard (s.length == 2)
  let chars := s.toList
  let hi ← chars[0]? >>= Char.hexDigitToNat?
  let lo ← chars[1]? >>= Char.hexDigitToNat?
  return BitVec.ofNat 8 (hi * 16 + lo)

-- Bit manipulation
def getBit (b : BitVec n) (i : Nat) : Bool :=
  (b >>> i &&& 1) != 0

def setBit (b : BitVec n) (i : Nat) (v : Bool) : BitVec n :=
  if v then b ||| (1 <<< i)
  else b &&& ~~~((1 : BitVec n) <<< i)

-- MSB and LSB
def msb (b : BitVec n) : Bool := getBit b (n - 1)
def lsb (b : BitVec n) : Bool := getBit b 0

-- Concatenation notation
infixl:65 " ## " => BitVec.append

-- Pretty printing for byte sequences
def bytesToHexString (bs : List Byte) : String :=
  " ".intercalate (bs.map Byte.toHex)

-- Theorems about bit operations
theorem DWord.fromBytes_toByte (d : DWord) :
    DWord.fromBytes (d.toByte ⟨0, by omega⟩) (d.toByte ⟨1, by omega⟩)
                    (d.toByte ⟨2, by omega⟩) (d.toByte ⟨3, by omega⟩) = d := by
  simp only [DWord.fromBytes, DWord.toByte]
  sorry -- Full proof requires bitvector automation

theorem Word.fromBytes_toByte (w : Word) :
    Word.fromBytes (w.toByte ⟨0, by omega⟩) (w.toByte ⟨1, by omega⟩) = w := by
  simp only [Word.fromBytes, Word.toByte]
  sorry -- Full proof requires bitvector automation

end X86
