/-
  Mem.lean - Memory model and processor state

  This module defines the memory model and processor state,
  matching the Coq mem.v and procstate.v from x86proved.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg

namespace X86

-- Memory is a partial function from addresses to bytes
-- We use a total function with default value for simplicity
structure Memory where
  read : DWord → Byte
deriving Inhabited

namespace Memory

-- Create an empty memory (all zeros)
def empty : Memory := ⟨fun _ => 0⟩

-- Write a single byte
def writeByte (m : Memory) (addr : DWord) (v : Byte) : Memory :=
  ⟨fun a => if a == addr then v else m.read a⟩

-- Read a byte
def readByte (m : Memory) (addr : DWord) : Byte :=
  m.read addr

-- Write a word (16-bit, little-endian)
def writeWord (m : Memory) (addr : DWord) (v : Word) : Memory :=
  m.writeByte addr (v.toByte ⟨0, by omega⟩)
   |>.writeByte (addr + 1) (v.toByte ⟨1, by omega⟩)

-- Read a word (little-endian)
def readWord (m : Memory) (addr : DWord) : Word :=
  Word.fromBytes (m.readByte addr) (m.readByte (addr + 1))

-- Write a dword (32-bit, little-endian)
def writeDWord (m : Memory) (addr : DWord) (v : DWord) : Memory :=
  m.writeByte addr (v.toByte ⟨0, by omega⟩)
   |>.writeByte (addr + 1) (v.toByte ⟨1, by omega⟩)
   |>.writeByte (addr + 2) (v.toByte ⟨2, by omega⟩)
   |>.writeByte (addr + 3) (v.toByte ⟨3, by omega⟩)

-- Read a dword (little-endian)
def readDWord (m : Memory) (addr : DWord) : DWord :=
  DWord.fromBytes
    (m.readByte addr)
    (m.readByte (addr + 1))
    (m.readByte (addr + 2))
    (m.readByte (addr + 3))

-- Write bytes from a list
def writeBytes (m : Memory) (addr : DWord) (bs : List Byte) : Memory :=
  (bs.zip (List.range bs.length)).foldl (fun m' (b, i) => m'.writeByte (addr + i.toUInt32.toNat) b) m

-- Read bytes to a list
def readBytes (m : Memory) (addr : DWord) (n : Nat) : List Byte :=
  List.range n |>.map fun i => m.readByte (addr + i.toUInt32.toNat)

end Memory

-- x86 Flags register
structure Flags where
  CF : Bool  -- Carry flag
  PF : Bool  -- Parity flag
  AF : Bool  -- Auxiliary carry flag
  ZF : Bool  -- Zero flag
  SF : Bool  -- Sign flag
  OF : Bool  -- Overflow flag
  DF : Bool  -- Direction flag
  IF : Bool  -- Interrupt flag
deriving Repr, DecidableEq, Inhabited

namespace Flags

-- Population count (number of 1 bits)
def popCount (n : Nat) : Nat :=
  if h : n == 0 then 0
  else (n % 2) + popCount (n / 2)
termination_by n
decreasing_by
  simp_wf
  have : n ≠ 0 := by simp_all
  omega

def empty : Flags := ⟨false, false, false, false, false, false, false, false⟩

-- Convert flags to a DWORD (EFLAGS format)
def toDWord (f : Flags) : DWord :=
  let bits := [
    (0, f.CF), (2, f.PF), (4, f.AF), (6, f.ZF),
    (7, f.SF), (9, f.IF), (10, f.DF), (11, f.OF)
  ]
  bits.foldl (fun acc (i, b) => if b then acc ||| (1 <<< i) else acc) 0

-- Create flags from DWORD
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

-- Compute arithmetic flags for a result
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

-- Register file: mapping from registers to values
structure RegFile where
  regs : AnyReg → DWord
deriving Inhabited

namespace RegFile

def empty : RegFile := ⟨fun _ => 0⟩

def read (rf : RegFile) (r : AnyReg) : DWord := rf.regs r
def readReg (rf : RegFile) (r : Reg) : DWord := rf.regs (.reg r)

def write (rf : RegFile) (r : AnyReg) (v : DWord) : RegFile :=
  ⟨fun r' => if r' == r then v else rf.regs r'⟩
def writeReg (rf : RegFile) (r : Reg) (v : DWord) : RegFile :=
  rf.write (.reg r) v

-- Read a byte register
def readByteReg (rf : RegFile) (r : ByteReg) : Byte :=
  let base := rf.readReg r.toReg
  if r.isHigh then base.toByte ⟨1, by omega⟩ else base.toByte ⟨0, by omega⟩

-- Write a byte register (preserves other bytes)
def writeByteReg (rf : RegFile) (r : ByteReg) (v : Byte) : RegFile :=
  let base := rf.readReg r.toReg
  let newVal := if r.isHigh then putRegPiece base .Ix1 v else putRegPiece base .Ix0 v
  rf.writeReg r.toReg newVal

-- Read a word register
def readWordReg (rf : RegFile) (r : WordReg) : Word :=
  let base := rf.readReg r.reg
  (base.truncate 16 : Word)

-- Write a word register (preserves high word)
def writeWordReg (rf : RegFile) (r : WordReg) (v : Word) : RegFile :=
  let base := rf.readReg r.reg
  let newVal := (base &&& 0xFFFF0000) ||| v.zeroExtend 32
  rf.writeReg r.reg newVal

-- Read a variable-width register
def readVReg (rf : RegFile) : {s : OpSize} → VReg s → VWord s
  | .Op8, r  => rf.readByteReg r
  | .Op16, r => rf.readWordReg r
  | .Op32, r => rf.readReg r

-- Write a variable-width register
def writeVReg (rf : RegFile) : {s : OpSize} → VReg s → VWord s → RegFile
  | .Op8, r, v  => rf.writeByteReg r v
  | .Op16, r, v => rf.writeWordReg r v
  | .Op32, r, v => rf.writeReg r v

end RegFile

-- Full processor state
structure ProcState where
  regs  : RegFile
  flags : Flags
  mem   : Memory
deriving Inhabited

namespace ProcState

def empty : ProcState := ⟨RegFile.empty, Flags.empty, Memory.empty⟩

-- Get EIP
def eip (s : ProcState) : DWord := s.regs.read .EIP

-- Set EIP
def setEIP (s : ProcState) (v : DWord) : ProcState :=
  { s with regs := s.regs.write .EIP v }

-- Get ESP
def esp (s : ProcState) : DWord := s.regs.readReg .ESP

-- Set ESP
def setESP (s : ProcState) (v : DWord) : ProcState :=
  { s with regs := s.regs.writeReg .ESP v }

-- Push a DWORD onto the stack
def push (s : ProcState) (v : DWord) : ProcState :=
  let newESP := s.esp - 4
  { s with
    regs := s.regs.writeReg .ESP newESP
    mem := s.mem.writeDWord newESP v }

-- Pop a DWORD from the stack
def pop (s : ProcState) : ProcState × DWord :=
  let v := s.mem.readDWord s.esp
  let newState := { s with regs := s.regs.writeReg .ESP (s.esp + 4) }
  (newState, v)

end ProcState

-- Cursor type for tracking positions in memory
structure Cursor where
  pos : DWord
deriving Repr, DecidableEq, Inhabited, Ord

instance : LE Cursor := ⟨fun c1 c2 => c1.pos.toNat ≤ c2.pos.toNat⟩
instance : LT Cursor := ⟨fun c1 c2 => c1.pos.toNat < c2.pos.toNat⟩

def Cursor.advance (c : Cursor) (n : Nat) : Cursor :=
  ⟨c.pos + n.toUInt32.toNat⟩

instance : HAdd Cursor Nat Cursor := ⟨Cursor.advance⟩

end X86
