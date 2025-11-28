/-
  X86DocsMain.lean - Entry point for building documentation site

  Run with: lake exe x86docs
-/

import VersoManual
import X86Docs

open Verso Doc
open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := true
  emitHtmlMulti := true
  htmlDepth := 2
  destination := "_out"

def main := manualMain (%doc X86Docs) (config := config)
