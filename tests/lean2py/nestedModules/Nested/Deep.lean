/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
import Nerodia

open Nerodia

/-- A Lean extension in a fully generated qualified package. -/
py_module "testgen.deep"

@[py_module_fn]
def greet : String :=
  "Hello from testgen.deep!"

@[py_module_attr]
def answer : Nat := 42
