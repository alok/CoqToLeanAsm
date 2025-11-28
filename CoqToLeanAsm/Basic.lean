/-
  CoqToLeanAsm - x86 Macro Assembler in Lean 4

  A port of "Coq: The World's Best Macro Assembler?" to Lean 4.
  Original paper by Kennedy, Benton, Jensen, and Dagand (PPDP 2013).

  This library provides:
  - Concrete bit/byte representations (using Lean's BitVec)
  - x86-32 instruction set encoding
  - Intel assembly syntax via Lean macros
  - Separation logic for program verification
  - Multi-pass assembler with label resolution
  - Control flow macros (if-then-else, while, procedures)

  Key modules:
  - Bits.lean: Bit vector operations
  - Reg.lean: x86 registers
  - Instr.lean: Instruction definitions
  - Mem.lean: Memory model and processor state
  - Encode.lean: Instruction encoding
  - Syntax.lean: Assembly syntax macros
  - SepLogic.lean: Separation logic predicates
  - Assembler.lean: Multi-pass assembler
  - Macros.lean: Control flow constructs
  - Examples.lean: Example programs
-/

import CoqToLeanAsm.Bits
import CoqToLeanAsm.Reg
import CoqToLeanAsm.Instr
import CoqToLeanAsm.Mem
import CoqToLeanAsm.Encode
import CoqToLeanAsm.Syntax
import CoqToLeanAsm.SepLogic
import CoqToLeanAsm.Assembler
import CoqToLeanAsm.Macros
import CoqToLeanAsm.Examples

/-
  This module re-exports all x86 assembler functionality.
  See the X86Docs Verso documentation for full usage examples.
-/

namespace X86

end X86
