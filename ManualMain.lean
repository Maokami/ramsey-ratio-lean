/-
Entry point that builds the Verso manual to HTML.
Run via `lake build manual` (executable target).
-/

import VersoManual
import Manual

open Verso Doc
open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  htmlDepth := 2

def main := manualMain (%doc Manual) (config := { config with })
