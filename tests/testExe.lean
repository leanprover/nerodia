/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

def main : IO Unit := do
  let o ← mkPyStr "hello" |>.toIO
  IO.println o.toString
