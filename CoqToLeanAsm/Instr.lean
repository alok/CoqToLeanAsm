/-
  Instr.lean - x86 Instruction definitions

  This module defines the x86 instruction set, matching the Coq instr.v
  from x86proved. Instructions are represented as an inductive type
  with explicit operand encoding.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg

namespace X86

-- Scale factors for SIB addressing
inductive Scale where
  | S1 | S2 | S4 | S8
deriving Repr, DecidableEq, Inhabited

def Scale.toNat : Scale → Nat
  | .S1 => 1
  | .S2 => 2
  | .S4 => 4
  | .S8 => 8

def Scale.toShift : Scale → Nat
  | .S1 => 0
  | .S2 => 1
  | .S4 => 2
  | .S8 => 3

-- Memory specification: [base + index*scale + offset]
-- base is optional VReg, index is optional NonSPReg with Scale
structure MemSpec where
  base   : Option Reg           -- Base register (optional)
  index  : Option (NonSPReg × Scale)  -- Index register with scale
  offset : DWord                -- Displacement
deriving Repr, DecidableEq, Inhabited

-- Shorthand constructors for MemSpec
def MemSpec.disp (d : DWord) : MemSpec := ⟨none, none, d⟩
def MemSpec.reg (r : Reg) : MemSpec := ⟨some r, none, 0⟩
def MemSpec.regDisp (r : Reg) (d : DWord) : MemSpec := ⟨some r, none, d⟩
def MemSpec.regIdx (r : Reg) (i : NonSPReg) (s : Scale) : MemSpec := ⟨some r, some (i, s), 0⟩
def MemSpec.regIdxDisp (r : Reg) (i : NonSPReg) (s : Scale) (d : DWord) : MemSpec :=
  ⟨some r, some (i, s), d⟩

-- Register or Memory operand
inductive RegMem (s : OpSize) where
  | R : VReg s → RegMem s
  | M : MemSpec → RegMem s

-- Register or Immediate operand
inductive RegImm (s : OpSize) where
  | I : VWord s → RegImm s
  | R : VReg s → RegImm s

-- Source operand (32-bit)
inductive Src where
  | I : DWord → Src      -- Immediate
  | M : MemSpec → Src    -- Memory
  | R : Reg → Src        -- Register
deriving Repr

instance : Coe DWord Src := ⟨.I⟩
instance : Coe MemSpec Src := ⟨.M⟩
instance : Coe Reg Src := ⟨.R⟩

-- Destination-Source pairs for binary operations
inductive DstSrc (s : OpSize) where
  | RR : VReg s → VReg s → DstSrc s       -- reg, reg
  | RM : VReg s → MemSpec → DstSrc s      -- reg, [mem]
  | MR : MemSpec → VReg s → DstSrc s      -- [mem], reg
  | RI : VReg s → VWord s → DstSrc s      -- reg, imm
  | MI : MemSpec → VWord s → DstSrc s     -- [mem], imm

-- Jump target (for relative jumps)
structure Tgt where
  addr : DWord
deriving Repr, DecidableEq, Inhabited

instance : Coe DWord Tgt := ⟨Tgt.mk⟩

-- Jump target (immediate, memory, or register)
inductive JmpTgt where
  | I : Tgt → JmpTgt       -- Immediate (relative)
  | M : MemSpec → JmpTgt   -- Memory indirect
  | R : Reg → JmpTgt       -- Register indirect
deriving Repr

instance : Coe Tgt JmpTgt := ⟨.I⟩
instance : Coe Reg JmpTgt := ⟨.R⟩

-- Shift count (CL register or immediate byte)
inductive ShiftCount where
  | CL : ShiftCount         -- Use CL register
  | I : Byte → ShiftCount   -- Immediate count
deriving Repr, DecidableEq, Inhabited

instance : Coe Byte ShiftCount := ⟨.I⟩

-- I/O port
inductive Port where
  | I : Byte → Port   -- Immediate port number
  | DX : Port         -- Use DX register
deriving Repr, DecidableEq, Inhabited

instance : Coe Byte Port := ⟨.I⟩

-- Binary ALU operations
inductive BinOp where
  | ADC | ADD | AND | CMP | OR | SBB | SUB | XOR
deriving Repr, DecidableEq, Inhabited

def BinOp.toNat : BinOp → Nat
  | .ADD => 0
  | .OR  => 1
  | .ADC => 2
  | .SBB => 3
  | .AND => 4
  | .SUB => 5
  | .XOR => 6
  | .CMP => 7

-- Unary operations
inductive UnaryOp where
  | INC | DEC | NOT | NEG
deriving Repr, DecidableEq, Inhabited

-- Bit operations
inductive BitOp where
  | BT | BTC | BTR | BTS
deriving Repr, DecidableEq, Inhabited

-- Shift/rotate operations
inductive ShiftOp where
  | ROL | ROR | RCL | RCR | SHL | SHR | SAL | SAR
deriving Repr, DecidableEq, Inhabited

def ShiftOp.toNat : ShiftOp → Nat
  | .ROL => 0
  | .ROR => 1
  | .RCL => 2
  | .RCR => 3
  | .SHL => 4  -- SAL is alias
  | .SHR => 5
  | .SAL => 4  -- Same as SHL
  | .SAR => 7

-- Condition codes (for conditional jumps and SETcc)
inductive Condition where
  | O    -- Overflow
  | B    -- Below (unsigned), Carry
  | Z    -- Zero, Equal
  | BE   -- Below or Equal (unsigned)
  | S    -- Sign (negative)
  | P    -- Parity even
  | L    -- Less (signed)
  | LE   -- Less or Equal (signed)
deriving Repr, DecidableEq, Inhabited

def Condition.toNat : Condition → Nat
  | .O  => 0
  | .B  => 2
  | .Z  => 4
  | .BE => 6
  | .S  => 8
  | .P  => 10
  | .L  => 12
  | .LE => 14

-- Condition with value (true = condition, false = negated condition)
-- E.g., (Z, true) = JZ, (Z, false) = JNZ
abbrev ConditionValue := Condition × Bool

-- Aliases for common conditions
def CC_O : ConditionValue := (.O, true)
def CC_NO : ConditionValue := (.O, false)
def CC_B : ConditionValue := (.B, true)
def CC_C : ConditionValue := (.B, true)   -- Carry = Below
def CC_NB : ConditionValue := (.B, false)
def CC_NC : ConditionValue := (.B, false)
def CC_AE : ConditionValue := (.B, false) -- Above or Equal = Not Below
def CC_Z : ConditionValue := (.Z, true)
def CC_E : ConditionValue := (.Z, true)   -- Equal = Zero
def CC_NZ : ConditionValue := (.Z, false)
def CC_NE : ConditionValue := (.Z, false)
def CC_BE : ConditionValue := (.BE, true)
def CC_NA : ConditionValue := (.BE, true) -- Not Above = Below or Equal
def CC_NBE : ConditionValue := (.BE, false)
def CC_A : ConditionValue := (.BE, false) -- Above = Not Below or Equal
def CC_S : ConditionValue := (.S, true)
def CC_NS : ConditionValue := (.S, false)
def CC_P : ConditionValue := (.P, true)
def CC_PE : ConditionValue := (.P, true)  -- Parity Even
def CC_NP : ConditionValue := (.P, false)
def CC_PO : ConditionValue := (.P, false) -- Parity Odd
def CC_L : ConditionValue := (.L, true)
def CC_NGE : ConditionValue := (.L, true) -- Not Greater or Equal
def CC_NL : ConditionValue := (.L, false)
def CC_GE : ConditionValue := (.L, false) -- Greater or Equal
def CC_LE : ConditionValue := (.LE, true)
def CC_NG : ConditionValue := (.LE, true) -- Not Greater
def CC_NLE : ConditionValue := (.LE, false)
def CC_G : ConditionValue := (.LE, false) -- Greater

-- The main instruction type
inductive Instr where
  -- Unary operations: INC, DEC, NOT, NEG
  | UOP (s : OpSize) (op : UnaryOp) (dst : RegMem s)

  -- Binary operations: ADD, SUB, AND, OR, XOR, CMP, ADC, SBB
  | BOP (s : OpSize) (op : BinOp) (ds : DstSrc s)

  -- Bit operations: BT, BTS, BTR, BTC
  | BITOP (op : BitOp) (dst : RegMem .Op32) (bit : Reg ⊕ Byte)

  -- TEST instruction
  | TESTOP (s : OpSize) (dst : RegMem s) (src : RegImm s)

  -- MOV instruction
  | MOVOP (s : OpSize) (ds : DstSrc s)

  -- MOV to segment register
  | MOVSegRM (dst : SegReg) (src : RegMem .Op16)

  -- MOV from segment register
  | MOVRMSeg (dst : RegMem .Op16) (src : SegReg)

  -- MOVZX/MOVSX
  | MOVX (signExtend : Bool) (s : OpSize) (dst : Reg) (src : RegMem s)

  -- Shift/rotate operations
  | SHIFTOP (s : OpSize) (op : ShiftOp) (dst : RegMem s) (count : ShiftCount)

  -- MUL (unsigned multiply)
  | MUL (s : OpSize) (src : RegMem s)

  -- IMUL (signed multiply, two-operand form)
  | IMUL (dst : Reg) (src : RegMem .Op32)

  -- LEA (load effective address)
  | LEA (dst : Reg) (src : MemSpec)

  -- XCHG
  | XCHG (s : OpSize) (reg : VReg s) (src : RegMem s)

  -- Conditional jump
  | JCCrel (cc : Condition) (cv : Bool) (tgt : Tgt)

  -- PUSH
  | PUSH (src : Src)

  -- PUSH segment register
  | PUSHSegR (r : SegReg)

  -- POP
  | POP (dst : RegMem .Op32)

  -- POP segment register
  | POPSegR (r : SegReg)

  -- CALL (relative)
  | CALLrel (tgt : JmpTgt)

  -- JMP (relative)
  | JMPrel (tgt : JmpTgt)

  -- Flag manipulation
  | CLC  -- Clear carry
  | STC  -- Set carry
  | CMC  -- Complement carry

  -- RET
  | RETOP (stackAdj : Word)

  -- OUT (write to I/O port)
  | OUTOP (s : OpSize) (port : Port)

  -- IN (read from I/O port)
  | INOP (s : OpSize) (port : Port)

  -- HLT (halt)
  | HLT

  -- NOP
  | NOP

  -- Intel SGX instructions
  | ENCLU
  | ENCLS

  -- Bad/unknown instruction
  | BADINSTR

-- String conversion for debugging
def BinOp.toString : BinOp → String
  | .ADD => "ADD"
  | .OR  => "OR"
  | .ADC => "ADC"
  | .SBB => "SBB"
  | .AND => "AND"
  | .SUB => "SUB"
  | .XOR => "XOR"
  | .CMP => "CMP"

def UnaryOp.toString : UnaryOp → String
  | .INC => "INC"
  | .DEC => "DEC"
  | .NOT => "NOT"
  | .NEG => "NEG"

def ShiftOp.toString : ShiftOp → String
  | .ROL => "ROL"
  | .ROR => "ROR"
  | .RCL => "RCL"
  | .RCR => "RCR"
  | .SHL => "SHL"
  | .SHR => "SHR"
  | .SAL => "SAL"
  | .SAR => "SAR"

instance : ToString BinOp := ⟨BinOp.toString⟩
instance : ToString UnaryOp := ⟨UnaryOp.toString⟩
instance : ToString ShiftOp := ⟨ShiftOp.toString⟩

end X86
