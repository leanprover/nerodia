/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia

open Nerodia

/- Mirrors the example in `PyIO.toIO`'s docstring. -/
public def main : IO Unit := do
  let pyVer ← PyIO.toIO do
    let sys ← Nerodia.import "sys"
    let ver ← sys.getAttrByString "version"
    return (← ver.str).toString
  IO.println pyVer
