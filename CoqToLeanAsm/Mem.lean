/-
  Mem.lean - Memory model and processor state

  This module defines the memory model and processor state,
  matching the Coq mem.v and procstate.v from x86proved.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg

namespace X86

/-- Memory model: maps 32-bit addresses to bytes.
Uses a total function with default value 0 for uninitialized memory. -/
structure Memory where
  /-- Read function mapping addresses to byte values -/
  read : DWord → Byte
deriving Inhabited

namespace Memory

/-- Create an empty memory initialized to all zeros -/
def empty : Memory := ⟨fun _ => 0⟩

/-- Write a single byte at the given address -/
def writeByte (m : Memory) (addr : DWord) (v : Byte) : Memory :=
  ⟨fun a => if a == addr then v else m.read a⟩

/-- Read a single byte from the given address -/
def readByte (m : Memory) (addr : DWord) : Byte :=
  m.read addr

/-- Write a 16-bit word at the given address (little-endian) -/
def writeWord (m : Memory) (addr : DWord) (v : Word) : Memory :=
  m.writeByte addr (v.toByte ⟨0, by omega⟩)
   |>.writeByte (addr + 1) (v.toByte ⟨1, by omega⟩)

/-- Read a 16-bit word from the given address (little-endian) -/
def readWord (m : Memory) (addr : DWord) : Word :=
  Word.fromBytes (m.readByte addr) (m.readByte (addr + 1))

/-- Write a 32-bit double word at the given address (little-endian) -/
def writeDWord (m : Memory) (addr : DWord) (v : DWord) : Memory :=
  m.writeByte addr (v.toByte ⟨0, by omega⟩)
   |>.writeByte (addr + 1) (v.toByte ⟨1, by omega⟩)
   |>.writeByte (addr + 2) (v.toByte ⟨2, by omega⟩)
   |>.writeByte (addr + 3) (v.toByte ⟨3, by omega⟩)

/-- Read a 32-bit double word from the given address (little-endian) -/
def readDWord (m : Memory) (addr : DWord) : DWord :=
  DWord.fromBytes
    (m.readByte addr)
    (m.readByte (addr + 1))
    (m.readByte (addr + 2))
    (m.readByte (addr + 3))

/-- Write a list of bytes starting at the given address -/
def writeBytes (m : Memory) (addr : DWord) (bs : List Byte) : Memory :=
  (bs.zip (List.range bs.length)).foldl (fun m' (b, i) => m'.writeByte (addr + i.toUInt32.toNat) b) m

/-- Read n bytes starting at the given address -/
def readBytes (m : Memory) (addr : DWord) (n : Nat) : List Byte :=
  List.range n |>.map fun i => m.readByte (addr + i.toUInt32.toNat)

end Memory

/-- x86 EFLAGS register containing status and control flags -/
structure Flags where
  /-- Carry flag: set on unsigned overflow -/
  CF : Bool
  /-- Parity flag: set if low byte has even number of 1 bits -/
  PF : Bool
  /-- Auxiliary carry flag: BCD arithmetic carry from bit 3 -/
  AF : Bool
  /-- Zero flag: set if result is zero -/
  ZF : Bool
  /-- Sign flag: set if result is negative (MSB = 1) -/
  SF : Bool
  /-- Overflow flag: set on signed overflow -/
  OF : Bool
  /-- Direction flag: controls string operation direction -/
  DF : Bool
  /-- Interrupt enable flag -/
  IF : Bool
deriving Repr, DecidableEq, Inhabited

namespace Flags

/-- Population count: number of 1 bits in the binary representation -/
def popCount (n : Nat) : Nat :=
  if h : n == 0 then 0
  else (n % 2) + popCount (n / 2)
termination_by n
decreasing_by
  simp_wf
  have : n ≠ 0 := by simp_all
  omega

/-- Create flags with all bits cleared -/
def empty : Flags := ⟨false, false, false, false, false, false, false, false⟩

/-- Convert flags to EFLAGS register format (32-bit) -/
def toDWord (f : Flags) : DWord :=
  let bits := [
    (0, f.CF), (2, f.PF), (4, f.AF), (6, f.ZF),
    (7, f.SF), (9, f.IF), (10, f.DF), (11, f.OF)
  ]
  bits.foldl (fun acc (i, b) => if b then acc ||| (1 <<< i) else acc) 0

/-- Parse flags from EFLAGS register format -/
def ofDWord (d : DWord) : Flags :=
  { CF := getBit d 0
  , PF := getBit d 2
  , AF := getBit d 4
  , ZF := getBit d 6
  , SF := getBit d 7
  , IF := getBit d 9
  , DF := getBit d 10
  , OF := getBit d 11
  }

/-- Compute flags for an arithmetic operation result -/
def arithmetic (result : DWord) (carry : Bool) (overflow : Bool) : Flags :=
  { CF := carry
  , PF := popCount (result.toNat % 256) % 2 == 0
  , AF := false  -- Simplified
  , ZF := result == 0
  , SF := msb result
  , OF := overflow
  , DF := false
  , IF := true
  }

end Flags

/-- Register file: maps registers to their 32-bit values -/
structure RegFile where
  /-- Function mapping registers to values -/
  regs : AnyReg → DWord
deriving Inhabited

namespace RegFile

/-- Create a register file with all registers set to zero -/
def empty : RegFile := ⟨fun _ => 0⟩

/-- Read a 32-bit value from any register -/
def read (rf : RegFile) (r : AnyReg) : DWord := rf.regs r
/-- Read a 32-bit value from a general-purpose register -/
def readReg (rf : RegFile) (r : Reg) : DWord := rf.regs (.reg r)

/-- Write a 32-bit value to any register -/
def write (rf : RegFile) (r : AnyReg) (v : DWord) : RegFile :=
  ⟨fun r' => if r' == r then v else rf.regs r'⟩
/-- Write a 32-bit value to a general-purpose register -/
def writeReg (rf : RegFile) (r : Reg) (v : DWord) : RegFile :=
  rf.write (.reg r) v

/-- Read an 8-bit value from a byte register -/
def readByteReg (rf : RegFile) (r : ByteReg) : Byte :=
  let base := rf.readReg r.toReg
  if r.isHigh then base.toByte ⟨1, by omega⟩ else base.toByte ⟨0, by omega⟩

/-- Write an 8-bit value to a byte register (preserves other bytes) -/
def writeByteReg (rf : RegFile) (r : ByteReg) (v : Byte) : RegFile :=
  let base := rf.readReg r.toReg
  let newVal := if r.isHigh then putRegPiece base .Ix1 v else putRegPiece base .Ix0 v
  rf.writeReg r.toReg newVal

/-- Read a 16-bit value from a word register -/
def readWordReg (rf : RegFile) (r : WordReg) : Word :=
  let base := rf.readReg r.reg
  (base.truncate 16 : Word)

/-- Write a 16-bit value to a word register (preserves high 16 bits) -/
def writeWordReg (rf : RegFile) (r : WordReg) (v : Word) : RegFile :=
  let base := rf.readReg r.reg
  let newVal := (base &&& 0xFFFF0000) ||| v.zeroExtend 32
  rf.writeReg r.reg newVal

/-- Read a variable-width register value -/
def readVReg (rf : RegFile) : {s : OpSize} → VReg s → VWord s
  | .Op8, r  => rf.readByteReg r
  | .Op16, r => rf.readWordReg r
  | .Op32, r => rf.readReg r

/-- Write a variable-width register value -/
def writeVReg (rf : RegFile) : {s : OpSize} → VReg s → VWord s → RegFile
  | .Op8, r, v  => rf.writeByteReg r v
  | .Op16, r, v => rf.writeWordReg r v
  | .Op32, r, v => rf.writeReg r v

end RegFile

/-- Full x86 processor state: registers, flags, and memory -/
structure ProcState where
  /-- General-purpose and special registers -/
  regs  : RegFile
  /-- EFLAGS register -/
  flags : Flags
  /-- Addressable memory -/
  mem   : Memory
deriving Inhabited

namespace ProcState

/-- Create an empty processor state with zeroed registers and memory -/
def empty : ProcState := ⟨RegFile.empty, Flags.empty, Memory.empty⟩

/-- Get the instruction pointer (EIP) -/
def eip (s : ProcState) : DWord := s.regs.read .EIP

/-- Set the instruction pointer (EIP) -/
def setEIP (s : ProcState) (v : DWord) : ProcState :=
  { s with regs := s.regs.write .EIP v }

/-- Get the stack pointer (ESP) -/
def esp (s : ProcState) : DWord := s.regs.readReg .ESP

/-- Set the stack pointer (ESP) -/
def setESP (s : ProcState) (v : DWord) : ProcState :=
  { s with regs := s.regs.writeReg .ESP v }

/-- Push a 32-bit value onto the stack (decrements ESP by 4) -/
def push (s : ProcState) (v : DWord) : ProcState :=
  let newESP := s.esp - 4
  { s with
    regs := s.regs.writeReg .ESP newESP
    mem := s.mem.writeDWord newESP v }

/-- Pop a 32-bit value from the stack (increments ESP by 4) -/
def pop (s : ProcState) : ProcState × DWord :=
  let v := s.mem.readDWord s.esp
  let newState := { s with regs := s.regs.writeReg .ESP (s.esp + 4) }
  (newState, v)

end ProcState

/-- Cursor for tracking position during assembly/encoding -/
structure Cursor where
  /-- Current byte position -/
  pos : DWord
deriving Repr, DecidableEq, Inhabited, Ord

instance : LE Cursor := ⟨fun c1 c2 => c1.pos.toNat ≤ c2.pos.toNat⟩
instance : LT Cursor := ⟨fun c1 c2 => c1.pos.toNat < c2.pos.toNat⟩

/-- Advance cursor by n bytes -/
def Cursor.advance (c : Cursor) (n : Nat) : Cursor :=
  ⟨c.pos + n.toUInt32.toNat⟩

instance : HAdd Cursor Nat Cursor := ⟨Cursor.advance⟩

end X86
