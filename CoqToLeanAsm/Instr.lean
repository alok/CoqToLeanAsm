/-
  Instr.lean - x86 Instruction definitions

  This module defines the x86 instruction set, matching the Coq instr.v
  from x86proved. Instructions are represented as an inductive type
  with explicit operand encoding.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg

namespace X86

/-- Scale factors for SIB (Scale-Index-Base) addressing: $index \times scale$ -/
inductive Scale where
  /-- Scale factor 1 -/
  | S1
  /-- Scale factor 2 -/
  | S2
  /-- Scale factor 4 -/
  | S4
  /-- Scale factor 8 -/
  | S8
deriving Repr, DecidableEq, Inhabited

/-- Convert scale to its numeric value -/
def Scale.toNat : Scale → Nat
  | .S1 => 1
  | .S2 => 2
  | .S4 => 4
  | .S8 => 8

/-- Convert scale to shift amount (log₂) -/
def Scale.toShift : Scale → Nat
  | .S1 => 0
  | .S2 => 1
  | .S4 => 2
  | .S8 => 3

/-- Memory operand specification: base + index×scale + offset -/
structure MemSpec where
  /-- Optional base register -/
  base   : Option Reg
  /-- Optional scaled index register (cannot be ESP) -/
  index  : Option (NonSPReg × Scale)
  /-- Displacement/offset value -/
  offset : DWord
deriving Repr, DecidableEq, Inhabited

/-- Displacement-only addressing -/
def MemSpec.disp (d : DWord) : MemSpec := ⟨none, none, d⟩
/-- Register-indirect addressing -/
def MemSpec.reg (r : Reg) : MemSpec := ⟨some r, none, 0⟩
/-- Register + displacement addressing -/
def MemSpec.regDisp (r : Reg) (d : DWord) : MemSpec := ⟨some r, none, d⟩
/-- Scaled index addressing: base + index×scale -/
def MemSpec.regIdx (r : Reg) (i : NonSPReg) (s : Scale) : MemSpec := ⟨some r, some (i, s), 0⟩
/-- Full SIB addressing: base + index×scale + disp -/
def MemSpec.regIdxDisp (r : Reg) (i : NonSPReg) (s : Scale) (d : DWord) : MemSpec :=
  ⟨some r, some (i, s), d⟩

/-- Operand that is either a register or memory location -/
inductive RegMem (s : OpSize) where
  /-- Register operand -/
  | R : VReg s → RegMem s
  /-- Memory operand -/
  | M : MemSpec → RegMem s

/-- Operand that is either a register or immediate value -/
inductive RegImm (s : OpSize) where
  /-- Immediate value -/
  | I : VWord s → RegImm s
  /-- Register operand -/
  | R : VReg s → RegImm s

/-- Source operand for 32-bit operations -/
inductive Src where
  /-- Immediate 32-bit value -/
  | I : DWord → Src
  /-- Memory location -/
  | M : MemSpec → Src
  /-- Register -/
  | R : Reg → Src
deriving Repr

instance : Coe DWord Src := ⟨.I⟩
instance : Coe MemSpec Src := ⟨.M⟩
instance : Coe Reg Src := ⟨.R⟩

/-- Destination-source pair for binary operations -/
inductive DstSrc (s : OpSize) where
  /-- Register to register -/
  | RR : VReg s → VReg s → DstSrc s
  /-- Register from memory -/
  | RM : VReg s → MemSpec → DstSrc s
  /-- Memory from register -/
  | MR : MemSpec → VReg s → DstSrc s
  /-- Register with immediate -/
  | RI : VReg s → VWord s → DstSrc s
  /-- Memory with immediate -/
  | MI : MemSpec → VWord s → DstSrc s

/-- Jump target address (for relative jumps) -/
structure Tgt where
  /-- Target address -/
  addr : DWord
deriving Repr, DecidableEq, Inhabited

instance : Coe DWord Tgt := ⟨Tgt.mk⟩

/-- Jump target: immediate address, memory indirect, or register indirect -/
inductive JmpTgt where
  /-- Direct/relative jump to address -/
  | I : Tgt → JmpTgt
  /-- Indirect jump through memory -/
  | M : MemSpec → JmpTgt
  /-- Indirect jump through register -/
  | R : Reg → JmpTgt
deriving Repr

instance : Coe Tgt JmpTgt := ⟨.I⟩
instance : Coe Reg JmpTgt := ⟨.R⟩

/-- Shift/rotate count: CL register or immediate byte -/
inductive ShiftCount where
  /-- Use CL register as count -/
  | CL : ShiftCount
  /-- Immediate count value -/
  | I : Byte → ShiftCount
deriving Repr, DecidableEq, Inhabited

instance : Coe Byte ShiftCount := ⟨.I⟩

/-- I/O port specification -/
inductive Port where
  /-- Immediate 8-bit port number -/
  | I : Byte → Port
  /-- Use DX register as port number -/
  | DX : Port
deriving Repr, DecidableEq, Inhabited

instance : Coe Byte Port := ⟨.I⟩

/-- Binary ALU operations -/
inductive BinOp where
  /-- Add with carry -/
  | ADC
  /-- Add -/
  | ADD
  /-- Bitwise AND -/
  | AND
  /-- Compare (subtract without storing) -/
  | CMP
  /-- Bitwise OR -/
  | OR
  /-- Subtract with borrow -/
  | SBB
  /-- Subtract -/
  | SUB
  /-- Bitwise XOR -/
  | XOR
deriving Repr, DecidableEq, Inhabited

/-- Encode binary operation to 3-bit opcode extension -/
def BinOp.toNat : BinOp → Nat
  | .ADD => 0
  | .OR  => 1
  | .ADC => 2
  | .SBB => 3
  | .AND => 4
  | .SUB => 5
  | .XOR => 6
  | .CMP => 7

/-- Unary ALU operations -/
inductive UnaryOp where
  /-- Increment by 1 -/
  | INC
  /-- Decrement by 1 -/
  | DEC
  /-- Bitwise NOT (one's complement) -/
  | NOT
  /-- Arithmetic negation (two's complement) -/
  | NEG
deriving Repr, DecidableEq, Inhabited

/-- Bit test operations -/
inductive BitOp where
  /-- Bit test -/
  | BT
  /-- Bit test and complement -/
  | BTC
  /-- Bit test and reset -/
  | BTR
  /-- Bit test and set -/
  | BTS
deriving Repr, DecidableEq, Inhabited

/-- Shift and rotate operations -/
inductive ShiftOp where
  /-- Rotate left -/
  | ROL
  /-- Rotate right -/
  | ROR
  /-- Rotate left through carry -/
  | RCL
  /-- Rotate right through carry -/
  | RCR
  /-- Shift left (multiply by 2) -/
  | SHL
  /-- Shift right (unsigned divide by 2) -/
  | SHR
  /-- Shift arithmetic left (same as SHL) -/
  | SAL
  /-- Shift arithmetic right (signed divide by 2) -/
  | SAR
deriving Repr, DecidableEq, Inhabited

/-- Encode shift operation to 3-bit opcode extension -/
def ShiftOp.toNat : ShiftOp → Nat
  | .ROL => 0
  | .ROR => 1
  | .RCL => 2
  | .RCR => 3
  | .SHL => 4  -- SAL is alias
  | .SHR => 5
  | .SAL => 4  -- Same as SHL
  | .SAR => 7

/-- Condition codes for conditional jumps and SETcc -/
inductive Condition where
  /-- Overflow (OF=1) -/
  | O
  /-- Below/Carry (CF=1, unsigned) -/
  | B
  /-- Zero/Equal (ZF=1) -/
  | Z
  /-- Below or Equal (CF=1 or ZF=1, unsigned) -/
  | BE
  /-- Sign/Negative (SF=1) -/
  | S
  /-- Parity Even (PF=1) -/
  | P
  /-- Less (SF≠OF, signed) -/
  | L
  /-- Less or Equal (ZF=1 or SF≠OF, signed) -/
  | LE
deriving Repr, DecidableEq, Inhabited

/-- Encode condition to 4-bit condition code -/
def Condition.toNat : Condition → Nat
  | .O  => 0
  | .B  => 2
  | .Z  => 4
  | .BE => 6
  | .S  => 8
  | .P  => 10
  | .L  => 12
  | .LE => 14

/-- Condition with polarity: (condition, true) tests condition,
(condition, false) tests negated condition -/
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
