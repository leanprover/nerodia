/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
import Nerodia

open Nerodia

/-- A Lean extension nested in a package provided by the project. -/
py_module "testpkg.ext"

@[py_module_fn]
def greet : String :=
  "Hello from testpkg.ext!"

@[py_module_fn]
def double (n : Nat) : Nat :=
  2 * n

@[py_module_attr "lean_str"]
def leanStr : String := "lean"
