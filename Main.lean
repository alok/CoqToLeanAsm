/-
  Main.lean - Entry point for CoqToLeanAsm

  Demonstrates the x86 macro assembler capabilities.
-/

import CoqToLeanAsm

open X86

-- Helper for right-padding strings
def String.padRight (s : String) (n : Nat) : String :=
  s ++ String.mk (List.replicate (n - s.length) ' ')

def main : IO Unit := do
  IO.println "=== CoqToLeanAsm: x86 Macro Assembler in Lean 4 ==="
  IO.println "Port of 'Coq: The World's Best Macro Assembler?' (Kennedy et al., 2013)"
  IO.println ""

  -- Example 1: Basic instruction encoding
  IO.println "--- Basic Instruction Encoding ---"
  let instrs : List (String × Instr) := [
    ("NOP", .NOP),
    ("RET", .RETOP 0),
    ("HLT", .HLT),
    ("PUSH EAX", .PUSH (.R EAX)),
    ("POP EBX", .POP (.R EBX)),
    ("INC ECX", .UOP .Op32 .INC (.R ECX)),
    ("DEC EDX", .UOP .Op32 .DEC (.R EDX))
  ]

  for (name, instr) in instrs do
    let bytes := encode 0 instr
    IO.println s!"  {name.padRight 12} -> {bytesToHexString bytes}"

  IO.println ""

  -- Example 2: MOV instruction variants
  IO.println "--- MOV Instruction Variants ---"
  let movs : List (String × Instr) := [
    ("MOV EAX, 42", .MOVOP .Op32 (.RI EAX 42)),
    ("MOV EAX, EBX", .MOVOP .Op32 (.RR EAX EBX)),
    ("MOV EAX, [EBX]", .MOVOP .Op32 (.RM EAX (MemSpec.reg EBX))),
    ("MOV EAX, [EBX+4]", .MOVOP .Op32 (.RM EAX (MemSpec.regDisp EBX 4))),
    ("MOV [EAX], EBX", .MOVOP .Op32 (.MR (MemSpec.reg EAX) EBX))
  ]

  for (name, instr) in movs do
    let bytes := encode 0 instr
    IO.println s!"  {name.padRight 18} -> {bytesToHexString bytes}"

  IO.println ""

  -- Example 3: Arithmetic operations
  IO.println "--- Arithmetic Operations ---"
  let arith : List (String × Instr) := [
    ("ADD EAX, 10", .BOP .Op32 .ADD (.RI EAX 10)),
    ("ADD EAX, EBX", .BOP .Op32 .ADD (.RR EAX EBX)),
    ("SUB EAX, ECX", .BOP .Op32 .SUB (.RR EAX ECX)),
    ("AND EAX, 0xFF", .BOP .Op32 .AND (.RI EAX 0xFF)),
    ("XOR EAX, EAX", .BOP .Op32 .XOR (.RR EAX EAX)),
    ("SHL EAX, 2", .SHIFTOP .Op32 .SHL (.R EAX) (.I 2))
  ]

  for (name, instr) in arith do
    let bytes := encode 0 instr
    IO.println s!"  {name.padRight 16} -> {bytesToHexString bytes}"

  IO.println ""

  -- Example 4: A complete program (factorial)
  IO.println "--- Complete Program: Factorial ---"
  IO.println "  ; Input: ECX = n"
  IO.println "  ; Output: EAX = n!"
  IO.println ""

  let factorialInstructions : List Instr := [
    .MOVOP .Op32 (.RI EAX 1),           -- MOV EAX, 1  ; result = 1
    .TESTOP .Op32 (.R ECX) (.R ECX),    -- TEST ECX, ECX
    .JCCrel .Z true ⟨0x1020⟩,           -- JZ done (placeholder address)
    -- loop:
    .IMUL EAX (.R ECX),                 -- IMUL EAX, ECX
    .UOP .Op32 .DEC (.R ECX),           -- DEC ECX
    .JCCrel .Z false ⟨0x100B⟩,          -- JNZ loop (placeholder address)
    -- done:
    .RETOP 0                            -- RET
  ]

  let prog := factorialInstructions.map ProgramItem.Instr
  match assemble 0x1000 prog with
  | .ok bytes =>
    IO.println "  Assembled bytes:"
    IO.println (hexDump bytes 0x1000)
    IO.println s!"\n  Total size: {bytes.length} bytes"
  | .error errs =>
    IO.println s!"  Errors: {repr errs}"

  IO.println ""

  -- Example 5: Using the macro builder
  IO.println "--- Using Macro Builder: Sum Array ---"
  IO.println "  ; Input: ESI = array ptr, ECX = count"
  IO.println "  ; Output: EAX = sum"

  let sumProg := ProgBuilder.buildProg do
    ProgBuilder.emit (.BOP .Op32 .XOR (.RR EAX EAX))  -- XOR EAX, EAX
    X86.«while»
      (ProgBuilder.emit (.TESTOP .Op32 (.R ECX) (.R ECX)))
      .Z false
      (do
        ProgBuilder.emit (.BOP .Op32 .ADD (.RM EAX (MemSpec.reg ESI)))
        ProgBuilder.emit (.BOP .Op32 .ADD (.RI ESI 4))
        ProgBuilder.emit (.UOP .Op32 .DEC (.R ECX)))

  match assemble 0x2000 sumProg with
  | .ok bytes =>
    IO.println "  Assembled bytes:"
    IO.println (hexDump bytes 0x2000)
    IO.println s!"\n  Total size: {bytes.length} bytes"
  | .error errs =>
    IO.println s!"  Errors: {repr errs}"

  IO.println ""
  IO.println "=== Done ==="
