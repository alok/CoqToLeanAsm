/-
  Syntax.lean - Assembly syntax helpers

  This module provides helpers for building x86 instructions
  in a readable way. The full macro-based Intel syntax is complex
  and we provide simpler helpers here.
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr

set_option linter.missingDocs false

namespace X86

-- Program is a list of instructions with optional labels
inductive ProgramItem where
  | Instr : Instr → ProgramItem
  | Label : String → ProgramItem
  | Data : List Byte → ProgramItem
  | Align : Nat → ProgramItem

abbrev Program := List ProgramItem

namespace Program

def empty : Program := []

def instr (i : Instr) : Program := [.Instr i]
def label (l : String) : Program := [.Label l]
def data (bs : List Byte) : Program := [.Data bs]
def align (n : Nat) : Program := [.Align n]

instance : Append Program := ⟨List.append⟩
instance : HAppend Program Program Program := ⟨List.append⟩

end Program

-- Label reference (resolved during assembly)
structure LabelRef where
  name : String
deriving DecidableEq

-- Instruction argument (for syntax)
inductive InstrArg where
  | Reg32 : Reg → InstrArg
  | Reg16 : WordReg → InstrArg
  | Reg8 : ByteReg → InstrArg
  | Mem : MemSpec → InstrArg
  | Imm32 : DWord → InstrArg
  | Imm16 : Word → InstrArg
  | Imm8 : Byte → InstrArg
  | LabelR : LabelRef → InstrArg

-- Convert common types to InstrArg
instance : Coe Reg InstrArg := ⟨.Reg32⟩
instance : Coe WordReg InstrArg := ⟨.Reg16⟩
instance : Coe ByteReg InstrArg := ⟨.Reg8⟩
instance : Coe MemSpec InstrArg := ⟨.Mem⟩
instance : Coe DWord InstrArg := ⟨.Imm32⟩
instance : Coe LabelRef InstrArg := ⟨.LabelR⟩

-- Helper to parse scale
def parseScale (n : Nat) : Scale :=
  match n with
  | 1 => .S1
  | 2 => .S2
  | 4 => .S4
  | 8 => .S8
  | _ => .S1

-- Convert register to NonSPReg if possible
def regToNonSP : Reg → Option NonSPReg
  | .nonSPReg r => some r
  | .ESP => none

-- Term-level helpers for building MemSpec
def mkMem (r : Reg) : MemSpec := MemSpec.reg r
def mkMemDisp (r : Reg) (d : Nat) : MemSpec := MemSpec.regDisp r (BitVec.ofNat 32 d)
def mkMemDispNeg (r : Reg) (d : Nat) : MemSpec := MemSpec.regDisp r (BitVec.ofNat 32 (0xFFFFFFFF - d + 1))
def mkMemIdx (r1 r2 : Reg) : MemSpec :=
  match regToNonSP r2 with
  | some nr => ⟨some r1, some (nr, .S1), 0⟩
  | none => ⟨some r1, none, 0⟩
def mkMemIdxScale (r1 r2 : Reg) (s : Nat) : MemSpec :=
  match regToNonSP r2 with
  | some nr => ⟨some r1, some (nr, parseScale s), 0⟩
  | none => ⟨some r1, none, 0⟩
def mkMemIdxScaleDisp (r1 r2 : Reg) (s d : Nat) : MemSpec :=
  match regToNonSP r2 with
  | some nr => ⟨some r1, some (nr, parseScale s), BitVec.ofNat 32 d⟩
  | none => ⟨some r1, none, BitVec.ofNat 32 d⟩
def mkMemIdxScaleDispNeg (r1 r2 : Reg) (s d : Nat) : MemSpec :=
  match regToNonSP r2 with
  | some nr => ⟨some r1, some (nr, parseScale s), BitVec.ofNat 32 (0xFFFFFFFF - d + 1)⟩
  | none => ⟨some r1, none, BitVec.ofNat 32 (0xFFFFFFFF - d + 1)⟩
def mkMemAbs (addr : Nat) : MemSpec := MemSpec.disp (BitVec.ofNat 32 addr)

-- Build MOV instruction from arguments
def mkMOV : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .MOVOP .Op32 (.RR r1 r2)
  | .Reg32 r, .Mem m => .MOVOP .Op32 (.RM r m)
  | .Mem m, .Reg32 r => .MOVOP .Op32 (.MR m r)
  | .Reg32 r, .Imm32 i => .MOVOP .Op32 (.RI r i)
  | .Mem m, .Imm32 i => .MOVOP .Op32 (.MI m i)
  | .Reg8 r1, .Reg8 r2 => .MOVOP .Op8 (.RR r1 r2)
  | .Reg8 r, .Mem m => .MOVOP .Op8 (.RM r m)
  | .Mem m, .Reg8 r => .MOVOP .Op8 (.MR m r)
  | .Reg8 r, .Imm8 i => .MOVOP .Op8 (.RI r i)
  | _, _ => .BADINSTR

-- Build ADD instruction
def mkADD : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .BOP .Op32 .ADD (.RR r1 r2)
  | .Reg32 r, .Mem m => .BOP .Op32 .ADD (.RM r m)
  | .Mem m, .Reg32 r => .BOP .Op32 .ADD (.MR m r)
  | .Reg32 r, .Imm32 i => .BOP .Op32 .ADD (.RI r i)
  | .Mem m, .Imm32 i => .BOP .Op32 .ADD (.MI m i)
  | .Reg8 r1, .Reg8 r2 => .BOP .Op8 .ADD (.RR r1 r2)
  | _, _ => .BADINSTR

-- Generic binary operation builder
def mkBinOp (op : BinOp) : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .BOP .Op32 op (.RR r1 r2)
  | .Reg32 r, .Mem m => .BOP .Op32 op (.RM r m)
  | .Mem m, .Reg32 r => .BOP .Op32 op (.MR m r)
  | .Reg32 r, .Imm32 i => .BOP .Op32 op (.RI r i)
  | .Mem m, .Imm32 i => .BOP .Op32 op (.MI m i)
  | .Reg8 r1, .Reg8 r2 => .BOP .Op8 op (.RR r1 r2)
  | .Reg8 r, .Mem m => .BOP .Op8 op (.RM r m)
  | .Mem m, .Reg8 r => .BOP .Op8 op (.MR m r)
  | .Reg8 r, .Imm8 i => .BOP .Op8 op (.RI r i)
  | .Mem m, .Imm8 i => .BOP .Op8 op (.MI m i)
  | _, _ => .BADINSTR

def mkSUB := mkBinOp .SUB
def mkAND := mkBinOp .AND
def mkOR := mkBinOp .OR
def mkXOR := mkBinOp .XOR
def mkCMP := mkBinOp .CMP
def mkADC := mkBinOp .ADC
def mkSBB := mkBinOp .SBB

-- Unary operation builder
def mkUnaryOp (op : UnaryOp) : InstrArg → Instr
  | .Reg32 r => .UOP .Op32 op (.R r)
  | .Mem m => .UOP .Op32 op (.M m)
  | .Reg8 r => .UOP .Op8 op (.R r)
  | _ => .BADINSTR

def mkINC := mkUnaryOp .INC
def mkDEC := mkUnaryOp .DEC
def mkNOT := mkUnaryOp .NOT
def mkNEG := mkUnaryOp .NEG

-- Shift operation builder
def mkShiftOp (op : ShiftOp) : InstrArg → InstrArg → Instr
  | .Reg32 r, .Imm32 i => .SHIFTOP .Op32 op (.R r) (.I (i.truncate 8))
  | .Mem m, .Imm32 i => .SHIFTOP .Op32 op (.M m) (.I (i.truncate 8))
  | .Reg32 r, .Reg8 .CL => .SHIFTOP .Op32 op (.R r) .CL
  | .Mem m, .Reg8 .CL => .SHIFTOP .Op32 op (.M m) .CL
  | _, _ => .BADINSTR

def mkSHL := mkShiftOp .SHL
def mkSHR := mkShiftOp .SHR
def mkSAR := mkShiftOp .SAR
def mkSAL := mkShiftOp .SAL
def mkROL := mkShiftOp .ROL
def mkROR := mkShiftOp .ROR

-- PUSH/POP
def mkPUSH : InstrArg → Instr
  | .Reg32 r => .PUSH (.R r)
  | .Mem m => .PUSH (.M m)
  | .Imm32 i => .PUSH (.I i)
  | _ => .BADINSTR

def mkPOP : InstrArg → Instr
  | .Reg32 r => .POP (.R r)
  | .Mem m => .POP (.M m)
  | _ => .BADINSTR

-- JMP/CALL
def mkJMP : InstrArg → Instr
  | .Reg32 r => .JMPrel (.R r)
  | .Mem m => .JMPrel (.M m)
  | .Imm32 i => .JMPrel (.I ⟨i⟩)
  | _ => .BADINSTR

def mkCALL : InstrArg → Instr
  | .Reg32 r => .CALLrel (.R r)
  | .Mem m => .CALLrel (.M m)
  | .Imm32 i => .CALLrel (.I ⟨i⟩)
  | _ => .BADINSTR

-- Conditional jump builder
def mkJCC (cc : Condition) (cv : Bool) : InstrArg → Instr
  | .Imm32 i => .JCCrel cc cv ⟨i⟩
  | _ => .BADINSTR

-- TEST
def mkTEST : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .TESTOP .Op32 (.R r1) (.R r2)
  | .Reg32 r, .Imm32 i => .TESTOP .Op32 (.R r) (.I i)
  | .Mem m, .Reg32 r => .TESTOP .Op32 (.M m) (.R r)
  | .Mem m, .Imm32 i => .TESTOP .Op32 (.M m) (.I i)
  | _, _ => .BADINSTR

-- LEA
def mkLEA : InstrArg → MemSpec → Instr
  | .Reg32 r, m => .LEA r m
  | _, _ => .BADINSTR

-- XCHG
def mkXCHG : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .XCHG .Op32 r1 (.R r2)
  | .Reg32 r, .Mem m => .XCHG .Op32 r (.M m)
  | _, _ => .BADINSTR

-- MUL
def mkMUL : InstrArg → Instr
  | .Reg32 r => .MUL .Op32 (.R r)
  | .Mem m => .MUL .Op32 (.M m)
  | _ => .BADINSTR

-- IMUL (two-operand)
def mkIMUL : InstrArg → InstrArg → Instr
  | .Reg32 r1, .Reg32 r2 => .IMUL r1 (.R r2)
  | .Reg32 r, .Mem m => .IMUL r (.M m)
  | _, _ => .BADINSTR

-- ============================================================================
-- Intel-style Assembly Syntax: x86! { ... }
-- ============================================================================
-- Write assembly that looks like you copied it from a .s file!

declare_syntax_cat asmLine

-- Labels
syntax ident ":" : asmLine

-- No-operand instructions
syntax "nop" : asmLine
syntax "ret" : asmLine
syntax "hlt" : asmLine

-- One-operand instructions
syntax "push" term : asmLine
syntax "pop" term : asmLine
syntax "inc" term : asmLine
syntax "dec" term : asmLine
syntax "not" term : asmLine
syntax "neg" term : asmLine
syntax "mul" term : asmLine

-- Two-operand instructions
syntax "mov" term "," term : asmLine
syntax "add" term "," term : asmLine
syntax "sub" term "," term : asmLine
syntax "and" term "," term : asmLine
syntax "or" term "," term : asmLine
syntax "xor" term "," term : asmLine
syntax "cmp" term "," term : asmLine
syntax "test" term "," term : asmLine
syntax "imul" term "," term : asmLine
syntax "xchg" term "," term : asmLine
syntax "shl" term "," term : asmLine
syntax "shr" term "," term : asmLine
syntax "lea" term "," term : asmLine

-- Jump instructions
syntax "jmp" term : asmLine
syntax "call" term : asmLine
syntax "jz" term : asmLine
syntax "jnz" term : asmLine
syntax "je" term : asmLine
syntax "jne" term : asmLine
syntax "jl" term : asmLine
syntax "jge" term : asmLine
syntax "jle" term : asmLine
syntax "jg" term : asmLine
syntax "jb" term : asmLine
syntax "jae" term : asmLine
syntax "jbe" term : asmLine
syntax "ja" term : asmLine

-- Helper syntax to elaborate a single asm line into a term (Program)
syntax "asm_line%" asmLine : term

-- Elaborate single assembly line via helper
macro_rules
  | `(asm_line% $lbl:ident :) => `(Program.label $(Lean.quote lbl.getId.toString))
  | `(asm_line% nop) => `(Program.instr Instr.NOP)
  | `(asm_line% ret) => `(Program.instr (Instr.RETOP 0))
  | `(asm_line% hlt) => `(Program.instr Instr.HLT)
  | `(asm_line% push $e) => `(Program.instr (mkPUSH $e))
  | `(asm_line% pop $e) => `(Program.instr (mkPOP $e))
  | `(asm_line% inc $e) => `(Program.instr (mkINC $e))
  | `(asm_line% dec $e) => `(Program.instr (mkDEC $e))
  | `(asm_line% not $e) => `(Program.instr (mkNOT $e))
  | `(asm_line% neg $e) => `(Program.instr (mkNEG $e))
  | `(asm_line% mul $e) => `(Program.instr (mkMUL $e))
  | `(asm_line% mov $dst, $src) => `(Program.instr (mkMOV $dst $src))
  | `(asm_line% add $dst, $src) => `(Program.instr (mkADD $dst $src))
  | `(asm_line% sub $dst, $src) => `(Program.instr (mkSUB $dst $src))
  | `(asm_line% and $dst, $src) => `(Program.instr (mkAND $dst $src))
  | `(asm_line% or $dst, $src) => `(Program.instr (mkOR $dst $src))
  | `(asm_line% xor $dst, $src) => `(Program.instr (mkXOR $dst $src))
  | `(asm_line% cmp $dst, $src) => `(Program.instr (mkCMP $dst $src))
  | `(asm_line% test $dst, $src) => `(Program.instr (mkTEST $dst $src))
  | `(asm_line% imul $dst, $src) => `(Program.instr (mkIMUL $dst $src))
  | `(asm_line% xchg $dst, $src) => `(Program.instr (mkXCHG $dst $src))
  | `(asm_line% shl $dst, $src) => `(Program.instr (mkSHL $dst $src))
  | `(asm_line% shr $dst, $src) => `(Program.instr (mkSHR $dst $src))
  | `(asm_line% lea $dst, $src) => `(Program.instr (mkLEA $dst $src))
  | `(asm_line% jmp $tgt) => `(Program.instr (mkJMP $tgt))
  | `(asm_line% call $tgt) => `(Program.instr (mkCALL $tgt))
  | `(asm_line% jz $tgt) => `(Program.instr (mkJCC Condition.Z true $tgt))
  | `(asm_line% jnz $tgt) => `(Program.instr (mkJCC Condition.Z false $tgt))
  | `(asm_line% je $tgt) => `(Program.instr (mkJCC Condition.Z true $tgt))
  | `(asm_line% jne $tgt) => `(Program.instr (mkJCC Condition.Z false $tgt))
  | `(asm_line% jl $tgt) => `(Program.instr (mkJCC Condition.L true $tgt))
  | `(asm_line% jge $tgt) => `(Program.instr (mkJCC Condition.L false $tgt))
  | `(asm_line% jle $tgt) => `(Program.instr (mkJCC Condition.LE true $tgt))
  | `(asm_line% jg $tgt) => `(Program.instr (mkJCC Condition.LE false $tgt))
  | `(asm_line% jb $tgt) => `(Program.instr (mkJCC Condition.B true $tgt))
  | `(asm_line% jae $tgt) => `(Program.instr (mkJCC Condition.B false $tgt))
  | `(asm_line% jbe $tgt) => `(Program.instr (mkJCC Condition.BE true $tgt))
  | `(asm_line% ja $tgt) => `(Program.instr (mkJCC Condition.BE false $tgt))

-- Assembly block: write x86 like a .s file!
syntax "x86!" "{" asmLine* "}" : term

-- Elaborate assembly block into a Program
macro_rules
  | `(x86! { }) => `(Program.empty)
  | `(x86! { $line:asmLine }) => `(asm_line% $line)
  | `(x86! { $line:asmLine $lines:asmLine* }) => `(asm_line% $line ++ x86! { $lines* })

end X86
