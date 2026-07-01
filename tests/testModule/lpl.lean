/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia

open Nerodia

/-!
Tests importing, from Lean, a Python module which uses Lean.
That is, Lean-to-Python-to-Lean (LPL) integration.
-/

public def main : IO Unit := do
  let greeting ← PyIO.toIO do
    let mod ← Nerodia.import "testmodule"
    (← mod.getAttrByString "greeting").str
  IO.println greeting
