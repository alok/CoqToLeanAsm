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

/-- General purpose registers excluding ESP (used in SIB index addressing) -/
inductive NonSPReg where
  /-- Accumulator -/
  | EAX
  /-- Base -/
  | EBX
  /-- Counter -/
  | ECX
  /-- Data -/
  | EDX
  /-- Source Index -/
  | ESI
  /-- Destination Index -/
  | EDI
  /-- Base Pointer -/
  | EBP
deriving Repr, DecidableEq, Inhabited

/-- All 32-bit general purpose registers -/
inductive Reg where
  /-- Non-ESP register -/
  | nonSPReg : NonSPReg → Reg
  /-- Stack Pointer -/
  | ESP : Reg
deriving Repr, DecidableEq, Inhabited

/-- Any register including EIP (instruction pointer) -/
inductive AnyReg where
  /-- General purpose register -/
  | reg : Reg → AnyReg
  /-- Instruction pointer -/
  | EIP : AnyReg
deriving Repr, DecidableEq, Inhabited

/-- x86 segment registers -/
inductive SegReg where
  /-- Code Segment -/
  | CS
  /-- Data Segment -/
  | DS
  /-- Stack Segment -/
  | SS
  /-- Extra Segment -/
  | ES
  /-- Additional Segment (386+) -/
  | FS
  /-- Additional Segment (386+) -/
  | GS
deriving Repr, DecidableEq, Inhabited

/-- 8-bit byte registers (low/high bytes of AX, BX, CX, DX) -/
inductive ByteReg where
  /-- Low byte of AX -/
  | AL
  /-- High byte of AX -/
  | AH
  /-- Low byte of BX -/
  | BL
  /-- High byte of BX -/
  | BH
  /-- Low byte of CX -/
  | CL
  /-- High byte of CX -/
  | CH
  /-- Low byte of DX -/
  | DL
  /-- High byte of DX -/
  | DH
deriving Repr, DecidableEq, Inhabited

/-- 16-bit word registers (lower 16 bits of 32-bit registers) -/
structure WordReg where
  /-- Underlying 32-bit register -/
  reg : Reg
deriving Repr, DecidableEq, Inhabited

instance : Coe NonSPReg Reg := ⟨Reg.nonSPReg⟩
instance : Coe Reg AnyReg := ⟨AnyReg.reg⟩

/-- Encode NonSPReg to its 3-bit binary representation -/
def NonSPReg.toNat : NonSPReg → Nat
  | .EAX => 0
  | .ECX => 1  -- Note: ECX is 1, not EBX!
  | .EDX => 2
  | .EBX => 3
  | .EBP => 5
  | .ESI => 6
  | .EDI => 7

/-- Encode Reg to its 3-bit binary representation -/
def Reg.toNat : Reg → Nat
  | .nonSPReg r => r.toNat
  | .ESP => 4

/-- Encode AnyReg to natural (EIP = 8, used internally) -/
def AnyReg.toNat : AnyReg → Nat
  | .reg r => r.toNat
  | .EIP => 8

/-- Encode SegReg to its 3-bit binary representation -/
def SegReg.toNat : SegReg → Nat
  | .CS => 0
  | .DS => 1
  | .SS => 2
  | .ES => 3
  | .FS => 4
  | .GS => 5

/-- Encode ByteReg to its 3-bit binary representation -/
def ByteReg.toNat : ByteReg → Nat
  | .AL => 0
  | .CL => 1
  | .DL => 2
  | .BL => 3
  | .AH => 4
  | .CH => 5
  | .DH => 6
  | .BH => 7

/-- Decode 3-bit encoding to Reg -/
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

/-- Decode 3-bit encoding to ByteReg -/
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

/-- Byte index within a 32-bit register (0 = LSB) -/
inductive RegIx where
  /-- Byte 0 (bits 0-7) -/
  | Ix0
  /-- Byte 1 (bits 8-15) -/
  | Ix1
  /-- Byte 2 (bits 16-23) -/
  | Ix2
  /-- Byte 3 (bits 24-31) -/
  | Ix3
deriving Repr, DecidableEq, Inhabited

/-- A piece of a register (register + byte index) -/
structure RegPiece where
  /-- The register -/
  reg : AnyReg
  /-- Which byte -/
  ix : RegIx
deriving Repr, DecidableEq

/-- Extract a byte from a DWord at the given index -/
def getRegPiece (v : DWord) : RegIx → Byte
  | .Ix0 => v.toByte ⟨0, by omega⟩
  | .Ix1 => v.toByte ⟨1, by omega⟩
  | .Ix2 => v.toByte ⟨2, by omega⟩
  | .Ix3 => v.toByte ⟨3, by omega⟩

/-- Insert a byte into a DWord at the given index -/
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

/-- Variable-width register type indexed by operand size -/
def VReg : OpSize → Type
  | .Op8  => ByteReg
  | .Op16 => WordReg
  | .Op32 => Reg

/-- Variable-width register including EIP for 32-bit -/
def VRegAny : OpSize → Type
  | .Op8  => ByteReg
  | .Op16 => WordReg
  | .Op32 => AnyReg

instance : Coe Reg (VReg .Op32) := ⟨id⟩
instance : Coe WordReg (VReg .Op16) := ⟨id⟩
instance : Coe ByteReg (VReg .Op8) := ⟨id⟩
instance : Coe AnyReg (VRegAny .Op32) := ⟨id⟩

/-- Convert VReg to VRegAny (widens to include EIP for 32-bit) -/
def VReg.toVRegAny : {s : OpSize} → VReg s → VRegAny s
  | .Op8, r => r
  | .Op16, r => r
  | .Op32, r => AnyReg.reg r

/-- Get the base 32-bit register for an 8-bit register -/
def ByteReg.toReg : ByteReg → Reg
  | .AL | .AH => .nonSPReg .EAX
  | .BL | .BH => .nonSPReg .EBX
  | .CL | .CH => .nonSPReg .ECX
  | .DL | .DH => .nonSPReg .EDX

/-- Check if a byte register accesses the high byte (AH, BH, CH, DH) -/
def ByteReg.isHigh : ByteReg → Bool
  | .AH | .BH | .CH | .DH => true
  | _ => false

/-- Get the register piece (register + byte index) for a byte register -/
def ByteReg.toRegPiece : ByteReg → RegPiece
  | .AL => ⟨.reg (.nonSPReg .EAX), .Ix0⟩
  | .AH => ⟨.reg (.nonSPReg .EAX), .Ix1⟩
  | .BL => ⟨.reg (.nonSPReg .EBX), .Ix0⟩
  | .BH => ⟨.reg (.nonSPReg .EBX), .Ix1⟩
  | .CL => ⟨.reg (.nonSPReg .ECX), .Ix0⟩
  | .CH => ⟨.reg (.nonSPReg .ECX), .Ix1⟩
  | .DL => ⟨.reg (.nonSPReg .EDX), .Ix0⟩
  | .DH => ⟨.reg (.nonSPReg .EDX), .Ix1⟩

-- Register abbreviations for assembly syntax
/-- Accumulator register -/
abbrev EAX : Reg := .nonSPReg .EAX
/-- Base register -/
abbrev EBX : Reg := .nonSPReg .EBX
/-- Counter register -/
abbrev ECX : Reg := .nonSPReg .ECX
/-- Data register -/
abbrev EDX : Reg := .nonSPReg .EDX
/-- Source index register -/
abbrev ESI : Reg := .nonSPReg .ESI
/-- Destination index register -/
abbrev EDI : Reg := .nonSPReg .EDI
/-- Base pointer register -/
abbrev EBP : Reg := .nonSPReg .EBP
/-- Stack pointer register -/
abbrev ESP : Reg := .ESP

/-- 16-bit accumulator -/
abbrev AX : WordReg := ⟨EAX⟩
/-- 16-bit base -/
abbrev BX : WordReg := ⟨EBX⟩
/-- 16-bit counter -/
abbrev CX : WordReg := ⟨ECX⟩
/-- 16-bit data -/
abbrev DX : WordReg := ⟨EDX⟩
/-- 16-bit source index -/
abbrev SI : WordReg := ⟨ESI⟩
/-- 16-bit destination index -/
abbrev DI : WordReg := ⟨EDI⟩
/-- 16-bit base pointer -/
abbrev BP : WordReg := ⟨EBP⟩
/-- 16-bit stack pointer -/
abbrev SP : WordReg := ⟨ESP⟩

/-- Low byte of AX -/
abbrev AL : ByteReg := .AL
/-- High byte of AX -/
abbrev AH : ByteReg := .AH
/-- Low byte of BX -/
abbrev BL : ByteReg := .BL
/-- High byte of BX -/
abbrev BH : ByteReg := .BH
/-- Low byte of CX -/
abbrev CL : ByteReg := .CL
/-- High byte of CX -/
abbrev CH : ByteReg := .CH
/-- Low byte of DX -/
abbrev DL : ByteReg := .DL
/-- High byte of DX -/
abbrev DH : ByteReg := .DH

/-- Code segment -/
abbrev CS : SegReg := .CS
/-- Data segment -/
abbrev DS : SegReg := .DS
/-- Stack segment -/
abbrev SS : SegReg := .SS
/-- Extra segment -/
abbrev ES : SegReg := .ES
/-- Additional segment -/
abbrev FS : SegReg := .FS
/-- Additional segment -/
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
