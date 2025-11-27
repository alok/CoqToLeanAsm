/-
  Encode.lean - Instruction encoding (assembly to bytes)

  This module encodes x86 instructions into their binary representation,
  matching the Coq instrcodec.v from x86proved.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Mem

namespace X86

-- ByteWriter monad for emitting bytes
structure ByteWriter (α : Type) where
  run : List Byte → (α × List Byte)

namespace ByteWriter

def pure (a : α) : ByteWriter α := ⟨fun bs => (a, bs)⟩
def bind (m : ByteWriter α) (f : α → ByteWriter β) : ByteWriter β :=
  ⟨fun bs => let (a, bs') := m.run bs; (f a).run bs'⟩

instance : Monad ByteWriter where
  pure := pure
  bind := bind

-- Emit a single byte
def emitByte (b : Byte) : ByteWriter Unit :=
  ⟨fun bs => ((), bs ++ [b])⟩

-- Emit a word (little-endian)
def emitWord (w : Word) : ByteWriter Unit :=
  ⟨fun bs => ((), bs ++ [w.toByte ⟨0, by omega⟩, w.toByte ⟨1, by omega⟩])⟩

-- Emit a dword (little-endian)
def emitDWord (d : DWord) : ByteWriter Unit :=
  ⟨fun bs => ((), bs ++ [
    d.toByte ⟨0, by omega⟩,
    d.toByte ⟨1, by omega⟩,
    d.toByte ⟨2, by omega⟩,
    d.toByte ⟨3, by omega⟩
  ])⟩

-- Emit variable-sized word
def emitVWord : {s : OpSize} → VWord s → ByteWriter Unit
  | .Op8, b  => emitByte b
  | .Op16, w => emitWord w
  | .Op32, d => emitDWord d

-- Execute and get result
def execute (m : ByteWriter α) : List Byte :=
  (m.run []).2

end ByteWriter

-- ModR/M and SIB encoding
namespace ModRM

-- Build ModR/M byte
-- mod: 2 bits, reg: 3 bits, rm: 3 bits
def build (mod : Nat) (reg : Nat) (rm : Nat) : Byte :=
  BitVec.ofNat 8 ((mod % 4 * 64) + (reg % 8 * 8) + (rm % 8))

-- Build SIB byte
-- scale: 2 bits, index: 3 bits, base: 3 bits
def buildSIB (scale : Nat) (index : Nat) (base : Nat) : Byte :=
  BitVec.ofNat 8 ((scale % 4 * 64) + (index % 8 * 8) + (base % 8))

-- Determine if displacement is needed and its size
def dispSize (d : DWord) : Nat :=
  if d == 0 then 0
  else if d.toNat ≤ 127 || d.toNat ≥ 0xFFFFFF80 then 1  -- fits in signed byte
  else 4

-- Encode register operand (mod=11)
def encodeReg (reg : Nat) (rm : Nat) : ByteWriter Unit :=
  ByteWriter.emitByte (build 3 reg rm)

-- Encode memory operand
def encodeMem (reg : Nat) (m : MemSpec) : ByteWriter Unit := do
  match m.base, m.index with
  | none, none =>
    -- [disp32]
    ByteWriter.emitByte (build 0 reg 5)
    ByteWriter.emitDWord m.offset
  | some (.nonSPReg .EBP), none =>
    -- [EBP + disp] - EBP always needs displacement
    if m.offset == 0 then
      ByteWriter.emitByte (build 1 reg 5)
      ByteWriter.emitByte 0
    else if dispSize m.offset == 1 then
      ByteWriter.emitByte (build 1 reg 5)
      ByteWriter.emitByte (m.offset.truncate 8)
    else
      ByteWriter.emitByte (build 2 reg 5)
      ByteWriter.emitDWord m.offset
  | some .ESP, none =>
    -- [ESP + disp] - needs SIB byte
    let dsize := dispSize m.offset
    let mod := if m.offset == 0 then 0 else if dsize == 1 then 1 else 2
    ByteWriter.emitByte (build mod reg 4)
    ByteWriter.emitByte (buildSIB 0 4 4)  -- no index, ESP base
    if m.offset != 0 then
      if dsize == 1 then ByteWriter.emitByte (m.offset.truncate 8)
      else ByteWriter.emitDWord m.offset
  | some base, none =>
    -- [reg + disp]
    let baseNum := base.toNat
    let dsize := dispSize m.offset
    if m.offset == 0 then
      ByteWriter.emitByte (build 0 reg baseNum)
    else if dsize == 1 then
      ByteWriter.emitByte (build 1 reg baseNum)
      ByteWriter.emitByte (m.offset.truncate 8)
    else
      ByteWriter.emitByte (build 2 reg baseNum)
      ByteWriter.emitDWord m.offset
  | some .ESP, some (idx, scale) =>
    -- [ESP + idx*scale + disp]
    let dsize := dispSize m.offset
    let mod := if m.offset == 0 then 0 else if dsize == 1 then 1 else 2
    ByteWriter.emitByte (build mod reg 4)
    ByteWriter.emitByte (buildSIB scale.toShift idx.toNat 4)
    if m.offset != 0 then
      if dsize == 1 then ByteWriter.emitByte (m.offset.truncate 8)
      else ByteWriter.emitDWord m.offset
  | some base, some (idx, scale) =>
    -- [base + idx*scale + disp]
    let baseNum := base.toNat
    let dsize := dispSize m.offset
    let mod := if m.offset == 0 && baseNum != 5 then 0
               else if dsize == 1 || (m.offset == 0 && baseNum == 5) then 1
               else 2
    ByteWriter.emitByte (build mod reg 4)
    ByteWriter.emitByte (buildSIB scale.toShift idx.toNat baseNum)
    if mod == 1 then ByteWriter.emitByte (m.offset.truncate 8)
    else if mod == 2 then ByteWriter.emitDWord m.offset
  | none, some (idx, scale) =>
    -- [idx*scale + disp32]
    ByteWriter.emitByte (build 0 reg 4)
    ByteWriter.emitByte (buildSIB scale.toShift idx.toNat 5)
    ByteWriter.emitDWord m.offset

-- Encode RegMem operand
def encodeRegMem (reg : Nat) : {s : OpSize} → RegMem s → ByteWriter Unit
  | .Op8, .R r  => encodeReg reg r.toNat
  | .Op16, .R r => encodeReg reg r.reg.toNat
  | .Op32, .R r => encodeReg reg r.toNat
  | _, .M m     => encodeMem reg m

end ModRM

-- Main instruction encoder
def encodeInstr (addr : DWord) : Instr → ByteWriter Unit
  -- NOP
  | .NOP => ByteWriter.emitByte 0x90

  -- HLT
  | .HLT => ByteWriter.emitByte 0xF4

  -- CLC, STC, CMC
  | .CLC => ByteWriter.emitByte 0xF8
  | .STC => ByteWriter.emitByte 0xF9
  | .CMC => ByteWriter.emitByte 0xF5

  -- RET
  | .RETOP stackAdj =>
    if stackAdj == 0 then ByteWriter.emitByte 0xC3
    else do ByteWriter.emitByte 0xC2; ByteWriter.emitWord stackAdj

  -- Binary operations (ADD, SUB, etc.)
  | .BOP s op ds => do
    let opNum := op.toNat
    match s, ds with
    -- AL, imm8
    | .Op8, .RI r imm =>
      match r with
      | .AL => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 4))
        ByteWriter.emitByte imm
      | _ => do
        ByteWriter.emitByte 0x80
        ModRM.encodeReg opNum r.toNat
        ByteWriter.emitByte imm
    -- EAX, imm32
    | .Op32, .RI r imm =>
      match r with
      | .nonSPReg .EAX => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 5))
        ByteWriter.emitDWord imm
      | _ => do
        ByteWriter.emitByte 0x81
        ModRM.encodeReg opNum r.toNat
        ByteWriter.emitDWord imm
    -- reg, reg
    | .Op32, .RR dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 1))
        ModRM.encodeReg src.toNat dst.toNat
    | .Op8, .RR dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8))
        ModRM.encodeReg src.toNat dst.toNat
    -- reg, [mem]
    | .Op32, .RM dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 3))
        ModRM.encodeMem dst.toNat src
    | .Op8, .RM dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 2))
        ModRM.encodeMem dst.toNat src
    -- [mem], reg
    | .Op32, .MR dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8 + 1))
        ModRM.encodeMem src.toNat dst
    | .Op8, .MR dst src => do
        ByteWriter.emitByte (BitVec.ofNat 8 (opNum * 8))
        ModRM.encodeMem src.toNat dst
    -- [mem], imm
    | .Op32, .MI dst imm => do
        ByteWriter.emitByte 0x81
        ModRM.encodeMem opNum dst
        ByteWriter.emitDWord imm
    | .Op8, .MI dst imm => do
        ByteWriter.emitByte 0x80
        ModRM.encodeMem opNum dst
        ByteWriter.emitByte imm
    -- 16-bit versions
    | .Op16, _ => do
        ByteWriter.emitByte 0x66  -- operand size prefix
        -- Then encode as 32-bit (simplified)
        ByteWriter.pure ()

  -- Unary operations (INC, DEC, NOT, NEG)
  | .UOP s op dst => do
    match op with
    | .INC =>
      match s with
      | .Op32 =>
        match dst with
        | .R r => ByteWriter.emitByte (BitVec.ofNat 8 (0x40 + r.toNat))
        | .M m => do ByteWriter.emitByte 0xFF; ModRM.encodeMem 0 m
      | .Op8 => do ByteWriter.emitByte 0xFE; ModRM.encodeRegMem 0 dst
      | .Op16 => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xFF; ModRM.encodeRegMem 0 dst
    | .DEC =>
      match s with
      | .Op32 =>
        match dst with
        | .R r => ByteWriter.emitByte (BitVec.ofNat 8 (0x48 + r.toNat))
        | .M m => do ByteWriter.emitByte 0xFF; ModRM.encodeMem 1 m
      | .Op8 => do ByteWriter.emitByte 0xFE; ModRM.encodeRegMem 1 dst
      | .Op16 => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xFF; ModRM.encodeRegMem 1 dst
    | .NOT => do
      match s with
      | .Op32 => ByteWriter.emitByte 0xF7
      | .Op8 => ByteWriter.emitByte 0xF6
      | .Op16 => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xF7
      ModRM.encodeRegMem 2 dst
    | .NEG => do
      match s with
      | .Op32 => ByteWriter.emitByte 0xF7
      | .Op8 => ByteWriter.emitByte 0xF6
      | .Op16 => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xF7
      ModRM.encodeRegMem 3 dst

  -- MOV
  | .MOVOP s ds => do
    match s, ds with
    | .Op32, .RR dst src => do
        ByteWriter.emitByte 0x89
        ModRM.encodeReg src.toNat dst.toNat
    | .Op32, .RM dst src => do
        ByteWriter.emitByte 0x8B
        ModRM.encodeMem dst.toNat src
    | .Op32, .MR dst src => do
        ByteWriter.emitByte 0x89
        ModRM.encodeMem src.toNat dst
    | .Op32, .RI dst imm =>
        -- MOV reg, imm32 uses short form
        ByteWriter.emitByte (BitVec.ofNat 8 (0xB8 + dst.toNat))
        ByteWriter.emitDWord imm
    | .Op32, .MI dst imm => do
        ByteWriter.emitByte 0xC7
        ModRM.encodeMem 0 dst
        ByteWriter.emitDWord imm
    | .Op8, .RR dst src => do
        ByteWriter.emitByte 0x88
        ModRM.encodeReg src.toNat dst.toNat
    | .Op8, .RM dst src => do
        ByteWriter.emitByte 0x8A
        ModRM.encodeMem dst.toNat src
    | .Op8, .MR dst src => do
        ByteWriter.emitByte 0x88
        ModRM.encodeMem src.toNat dst
    | .Op8, .RI dst imm =>
        ByteWriter.emitByte (BitVec.ofNat 8 (0xB0 + dst.toNat))
        ByteWriter.emitByte imm
    | .Op8, .MI dst imm => do
        ByteWriter.emitByte 0xC6
        ModRM.encodeMem 0 dst
        ByteWriter.emitByte imm
    | .Op16, _ => do
        ByteWriter.emitByte 0x66
        ByteWriter.pure ()

  -- PUSH
  | .PUSH src =>
    match src with
    | .R r => ByteWriter.emitByte (BitVec.ofNat 8 (0x50 + r.toNat))
    | .I imm => do ByteWriter.emitByte 0x68; ByteWriter.emitDWord imm
    | .M m => do ByteWriter.emitByte 0xFF; ModRM.encodeMem 6 m

  -- POP
  | .POP dst =>
    match dst with
    | .R r => ByteWriter.emitByte (BitVec.ofNat 8 (0x58 + r.toNat))
    | .M m => do ByteWriter.emitByte 0x8F; ModRM.encodeMem 0 m

  -- LEA
  | .LEA dst src => do
    ByteWriter.emitByte 0x8D
    ModRM.encodeMem dst.toNat src

  -- Conditional jump (short form for now)
  | .JCCrel cc cv tgt => do
    let offset := tgt.addr.toInt - (addr.toInt + 2)  -- 2-byte instruction
    let ccByte := cc.toNat + (if cv then 0 else 1)
    if offset >= -128 && offset <= 127 then
      ByteWriter.emitByte (BitVec.ofNat 8 (0x70 + ccByte))
      ByteWriter.emitByte (BitVec.ofInt 8 offset)
    else do
      -- Near jump (6 bytes)
      let offset' := tgt.addr.toInt - (addr.toInt + 6)
      ByteWriter.emitByte 0x0F
      ByteWriter.emitByte (BitVec.ofNat 8 (0x80 + ccByte))
      ByteWriter.emitDWord (BitVec.ofInt 32 offset')

  -- JMP
  | .JMPrel tgt =>
    match tgt with
    | .I t => do
      let offset := t.addr.toInt - (addr.toInt + 5)
      ByteWriter.emitByte 0xE9
      ByteWriter.emitDWord (BitVec.ofInt 32 offset)
    | .R r => do
      ByteWriter.emitByte 0xFF
      ModRM.encodeReg 4 r.toNat
    | .M m => do
      ByteWriter.emitByte 0xFF
      ModRM.encodeMem 4 m

  -- CALL
  | .CALLrel tgt =>
    match tgt with
    | .I t => do
      let offset := t.addr.toInt - (addr.toInt + 5)
      ByteWriter.emitByte 0xE8
      ByteWriter.emitDWord (BitVec.ofInt 32 offset)
    | .R r => do
      ByteWriter.emitByte 0xFF
      ModRM.encodeReg 2 r.toNat
    | .M m => do
      ByteWriter.emitByte 0xFF
      ModRM.encodeMem 2 m

  -- TEST
  | .TESTOP s dst src => do
    match s with
    | .Op32 =>
      match dst, src with
      | .R (.nonSPReg .EAX), .I imm => do
          ByteWriter.emitByte 0xA9
          ByteWriter.emitDWord imm
      | .R r, .I imm => do
          ByteWriter.emitByte 0xF7
          ModRM.encodeReg 0 r.toNat
          ByteWriter.emitDWord imm
      | .R r, .R r' => do
          ByteWriter.emitByte 0x85
          ModRM.encodeReg r'.toNat r.toNat
      | .M m, .I imm => do
          ByteWriter.emitByte 0xF7
          ModRM.encodeMem 0 m
          ByteWriter.emitDWord imm
      | .M m, .R r => do
          ByteWriter.emitByte 0x85
          ModRM.encodeMem r.toNat m
    | .Op8 =>
      match dst, src with
      | .R .AL, .I imm => do
          ByteWriter.emitByte 0xA8
          ByteWriter.emitByte imm
      | .R r, .I imm => do
          ByteWriter.emitByte 0xF6
          ModRM.encodeReg 0 r.toNat
          ByteWriter.emitByte imm
      | .R r, .R r' => do
          ByteWriter.emitByte 0x84
          ModRM.encodeReg r'.toNat r.toNat
      | .M m, .I imm => do
          ByteWriter.emitByte 0xF6
          ModRM.encodeMem 0 m
          ByteWriter.emitByte imm
      | .M m, .R r => do
          ByteWriter.emitByte 0x84
          ModRM.encodeMem r.toNat m
    | .Op16 => ByteWriter.pure ()

  -- Shift operations
  | .SHIFTOP s op dst count => do
    let opNum := op.toNat
    match s with
    | .Op32 =>
      match count with
      | .I c =>
        if c == 1 then do
          ByteWriter.emitByte 0xD1
          ModRM.encodeRegMem opNum dst
        else do
          ByteWriter.emitByte 0xC1
          ModRM.encodeRegMem opNum dst
          ByteWriter.emitByte c
      | .CL => do
        ByteWriter.emitByte 0xD3
        ModRM.encodeRegMem opNum dst
    | .Op8 =>
      match count with
      | .I c =>
        if c == 1 then do
          ByteWriter.emitByte 0xD0
          ModRM.encodeRegMem opNum dst
        else do
          ByteWriter.emitByte 0xC0
          ModRM.encodeRegMem opNum dst
          ByteWriter.emitByte c
      | .CL => do
        ByteWriter.emitByte 0xD2
        ModRM.encodeRegMem opNum dst
    | .Op16 => ByteWriter.pure ()

  -- IMUL (two-operand form)
  | .IMUL dst src => do
    ByteWriter.emitByte 0x0F
    ByteWriter.emitByte 0xAF
    ModRM.encodeRegMem dst.toNat src

  -- MUL
  | .MUL s src => do
    match s with
    | .Op32 => do ByteWriter.emitByte 0xF7; ModRM.encodeRegMem 4 src
    | .Op8 => do ByteWriter.emitByte 0xF6; ModRM.encodeRegMem 4 src
    | .Op16 => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xF7; ModRM.encodeRegMem 4 src

  -- XCHG
  | .XCHG s reg src => do
    match s with
    | .Op32 =>
      match reg, src with
      | .nonSPReg .EAX, .R r => ByteWriter.emitByte (BitVec.ofNat 8 (0x90 + r.toNat))
      | _, .R (.nonSPReg .EAX) => ByteWriter.emitByte (BitVec.ofNat 8 (0x90 + reg.toNat))
      | _, .R r => do ByteWriter.emitByte 0x87; ModRM.encodeReg reg.toNat r.toNat
      | _, .M m => do ByteWriter.emitByte 0x87; ModRM.encodeMem reg.toNat m
    | .Op8 => do
      ByteWriter.emitByte 0x86
      ModRM.encodeRegMem reg.toNat src
    | .Op16 => ByteWriter.pure ()

  -- I/O operations
  | .INOP s port =>
    match s, port with
    | .Op8, .I p => do ByteWriter.emitByte 0xE4; ByteWriter.emitByte p
    | .Op8, .DX => ByteWriter.emitByte 0xEC
    | .Op32, .I p => do ByteWriter.emitByte 0xE5; ByteWriter.emitByte p
    | .Op32, .DX => ByteWriter.emitByte 0xED
    | .Op16, .I p => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xE5; ByteWriter.emitByte p
    | .Op16, .DX => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xED

  | .OUTOP s port =>
    match s, port with
    | .Op8, .I p => do ByteWriter.emitByte 0xE6; ByteWriter.emitByte p
    | .Op8, .DX => ByteWriter.emitByte 0xEE
    | .Op32, .I p => do ByteWriter.emitByte 0xE7; ByteWriter.emitByte p
    | .Op32, .DX => ByteWriter.emitByte 0xEF
    | .Op16, .I p => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xE7; ByteWriter.emitByte p
    | .Op16, .DX => do ByteWriter.emitByte 0x66; ByteWriter.emitByte 0xEF

  -- Other instructions (simplified)
  | .MOVX _ _ _ _ => ByteWriter.pure ()  -- TODO
  | .BITOP _ _ _ => ByteWriter.pure ()   -- TODO
  | .MOVSegRM _ _ => ByteWriter.pure ()  -- TODO
  | .MOVRMSeg _ _ => ByteWriter.pure ()  -- TODO
  | .PUSHSegR _ => ByteWriter.pure ()    -- TODO
  | .POPSegR _ => ByteWriter.pure ()     -- TODO
  | .ENCLU => ByteWriter.pure ()
  | .ENCLS => ByteWriter.pure ()
  | .BADINSTR => ByteWriter.pure ()

-- Encode a single instruction
def encode (addr : DWord) (instr : Instr) : List Byte :=
  ByteWriter.execute (encodeInstr addr instr)

-- Get the size of an encoded instruction
def instrSize (addr : DWord) (instr : Instr) : Nat :=
  (encode addr instr).length

end X86
