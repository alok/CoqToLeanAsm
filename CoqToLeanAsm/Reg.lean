/-
  Reg.lean - x86 Register definitions

  This module defines all x86-32 registers, matching the Coq reg.v
  from x86proved. Includes:
  - General purpose 32-bit registers (EAX, EBX, ECX, EDX, ESI, EDI, EBP, ESP)
  - 16-bit registers (AX, BX, CX, DX, SI, DI, BP, SP)
  - 8-bit registers (AL, AH, BL, BH, CL, CH, DL, DH)
  - Segment registers (CS, DS, SS, ES, FS, GS)
  - Special registers (EIP, EFLAGS)
-/

import CoqToLeanAsm.Bits

namespace X86

-- General purpose registers (excluding ESP for some addressing modes)
inductive NonSPReg where
  | EAX | EBX | ECX | EDX | ESI | EDI | EBP
deriving Repr, DecidableEq, Inhabited

-- All general purpose registers (including ESP)
inductive Reg where
  | nonSPReg : NonSPReg → Reg
  | ESP : Reg
deriving Repr, DecidableEq, Inhabited

-- Any register including EIP (but not EFLAGS)
inductive AnyReg where
  | reg : Reg → AnyReg
  | EIP : AnyReg
deriving Repr, DecidableEq, Inhabited

-- Segment registers
inductive SegReg where
  | CS | DS | SS | ES | FS | GS
deriving Repr, DecidableEq, Inhabited

-- 8-bit (byte) registers
inductive ByteReg where
  | AL | AH | BL | BH | CL | CH | DL | DH
deriving Repr, DecidableEq, Inhabited

-- 16-bit (word) registers - wrapping around Reg
structure WordReg where
  reg : Reg
deriving Repr, DecidableEq, Inhabited

-- Coercions for convenient usage
instance : Coe NonSPReg Reg := ⟨Reg.nonSPReg⟩
instance : Coe Reg AnyReg := ⟨AnyReg.reg⟩

-- Register encoding to natural numbers (for binary encoding)
def NonSPReg.toNat : NonSPReg → Nat
  | .EAX => 0
  | .ECX => 1  -- Note: ECX is 1, not EBX!
  | .EDX => 2
  | .EBX => 3
  | .EBP => 5
  | .ESI => 6
  | .EDI => 7

def Reg.toNat : Reg → Nat
  | .nonSPReg r => r.toNat
  | .ESP => 4

def AnyReg.toNat : AnyReg → Nat
  | .reg r => r.toNat
  | .EIP => 8

def SegReg.toNat : SegReg → Nat
  | .CS => 0
  | .DS => 1
  | .SS => 2
  | .ES => 3
  | .FS => 4
  | .GS => 5

def ByteReg.toNat : ByteReg → Nat
  | .AL => 0
  | .CL => 1
  | .DL => 2
  | .BL => 3
  | .AH => 4
  | .CH => 5
  | .DH => 6
  | .BH => 7

-- Decode natural to register
def Reg.ofNat? : Nat → Option Reg
  | 0 => some (.nonSPReg .EAX)
  | 1 => some (.nonSPReg .ECX)
  | 2 => some (.nonSPReg .EDX)
  | 3 => some (.nonSPReg .EBX)
  | 4 => some .ESP
  | 5 => some (.nonSPReg .EBP)
  | 6 => some (.nonSPReg .ESI)
  | 7 => some (.nonSPReg .EDI)
  | _ => none

def ByteReg.ofNat? : Nat → Option ByteReg
  | 0 => some .AL
  | 1 => some .CL
  | 2 => some .DL
  | 3 => some .BL
  | 4 => some .AH
  | 5 => some .CH
  | 6 => some .DH
  | 7 => some .BH
  | _ => none

-- Register pieces (for accessing bytes of 32-bit registers)
inductive RegIx where
  | Ix0 | Ix1 | Ix2 | Ix3
deriving Repr, DecidableEq, Inhabited

structure RegPiece where
  reg : AnyReg
  ix : RegIx
deriving Repr, DecidableEq

-- Get a byte from a DWORD based on register index
def getRegPiece (v : DWord) : RegIx → Byte
  | .Ix0 => v.toByte ⟨0, by omega⟩
  | .Ix1 => v.toByte ⟨1, by omega⟩
  | .Ix2 => v.toByte ⟨2, by omega⟩
  | .Ix3 => v.toByte ⟨3, by omega⟩

-- Put a byte into a DWORD at a register index position
def putRegPiece (v : DWord) (ix : RegIx) (b : Byte) : DWord :=
  let mask : DWord := match ix with
    | .Ix0 => 0xFFFFFF00
    | .Ix1 => 0xFFFF00FF
    | .Ix2 => 0xFF00FFFF
    | .Ix3 => 0x00FFFFFF
  let shifted : DWord := match ix with
    | .Ix0 => b.zeroExtend 32
    | .Ix1 => b.zeroExtend 32 <<< 8
    | .Ix2 => b.zeroExtend 32 <<< 16
    | .Ix3 => b.zeroExtend 32 <<< 24
  (v &&& mask) ||| shifted

-- Variable-width register type indexed by OpSize
def VReg : OpSize → Type
  | .Op8  => ByteReg
  | .Op16 => WordReg
  | .Op32 => Reg

-- Variable-width register including EIP for 32-bit
def VRegAny : OpSize → Type
  | .Op8  => ByteReg
  | .Op16 => WordReg
  | .Op32 => AnyReg

-- Coercions for VReg
instance : Coe Reg (VReg .Op32) := ⟨id⟩
instance : Coe WordReg (VReg .Op16) := ⟨id⟩
instance : Coe ByteReg (VReg .Op8) := ⟨id⟩
instance : Coe AnyReg (VRegAny .Op32) := ⟨id⟩

-- Convert VReg to VRegAny
def VReg.toVRegAny : {s : OpSize} → VReg s → VRegAny s
  | .Op8, r => r
  | .Op16, r => r
  | .Op32, r => AnyReg.reg r

-- Get the base 32-bit register for an 8-bit register
def ByteReg.toReg : ByteReg → Reg
  | .AL | .AH => .nonSPReg .EAX
  | .BL | .BH => .nonSPReg .EBX
  | .CL | .CH => .nonSPReg .ECX
  | .DL | .DH => .nonSPReg .EDX

-- Check if a byte register accesses the high byte
def ByteReg.isHigh : ByteReg → Bool
  | .AH | .BH | .CH | .DH => true
  | _ => false

-- Get the register piece for a byte register
def ByteReg.toRegPiece : ByteReg → RegPiece
  | .AL => ⟨.reg (.nonSPReg .EAX), .Ix0⟩
  | .AH => ⟨.reg (.nonSPReg .EAX), .Ix1⟩
  | .BL => ⟨.reg (.nonSPReg .EBX), .Ix0⟩
  | .BH => ⟨.reg (.nonSPReg .EBX), .Ix1⟩
  | .CL => ⟨.reg (.nonSPReg .ECX), .Ix0⟩
  | .CH => ⟨.reg (.nonSPReg .ECX), .Ix1⟩
  | .DL => ⟨.reg (.nonSPReg .EDX), .Ix0⟩
  | .DH => ⟨.reg (.nonSPReg .EDX), .Ix1⟩

-- Convenient names for registers (for use in assembly syntax)
abbrev EAX : Reg := .nonSPReg .EAX
abbrev EBX : Reg := .nonSPReg .EBX
abbrev ECX : Reg := .nonSPReg .ECX
abbrev EDX : Reg := .nonSPReg .EDX
abbrev ESI : Reg := .nonSPReg .ESI
abbrev EDI : Reg := .nonSPReg .EDI
abbrev EBP : Reg := .nonSPReg .EBP
abbrev ESP : Reg := .ESP

abbrev AX : WordReg := ⟨EAX⟩
abbrev BX : WordReg := ⟨EBX⟩
abbrev CX : WordReg := ⟨ECX⟩
abbrev DX : WordReg := ⟨EDX⟩
abbrev SI : WordReg := ⟨ESI⟩
abbrev DI : WordReg := ⟨EDI⟩
abbrev BP : WordReg := ⟨EBP⟩
abbrev SP : WordReg := ⟨ESP⟩

abbrev AL : ByteReg := .AL
abbrev AH : ByteReg := .AH
abbrev BL : ByteReg := .BL
abbrev BH : ByteReg := .BH
abbrev CL : ByteReg := .CL
abbrev CH : ByteReg := .CH
abbrev DL : ByteReg := .DL
abbrev DH : ByteReg := .DH

abbrev CS : SegReg := .CS
abbrev DS : SegReg := .DS
abbrev SS : SegReg := .SS
abbrev ES : SegReg := .ES
abbrev FS : SegReg := .FS
abbrev GS : SegReg := .GS

-- Theorems about register encoding
theorem Reg.toNat_lt_8 (r : Reg) : r.toNat < 8 := by
  cases r with
  | nonSPReg nr => cases nr <;> simp [toNat, NonSPReg.toNat]
  | ESP => simp [toNat]

theorem ByteReg.toNat_lt_8 (r : ByteReg) : r.toNat < 8 := by
  cases r <;> simp [toNat]

-- Roundtrip theorem
theorem Reg.ofNat_toNat (r : Reg) : Reg.ofNat? r.toNat = some r := by
  cases r with
  | nonSPReg nr => cases nr <;> rfl
  | ESP => rfl

end X86
