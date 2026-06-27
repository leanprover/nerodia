/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia.Compiler.Main

public def main (args : List String) : IO UInt32 := do
  Nerodia.Compiler.main args
