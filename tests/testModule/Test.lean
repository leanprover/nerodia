/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

/-- A Lean-to-Python test module. -/
py_module "testmodule"

/-- Return a greeting. -/
@[py_module_fn "greeting_for"]
def greetingFor (s : String) : String :=
  s!"Hello, {s}!"

/-- The standard greeting. -/
@[py_module_attr]
def greeting : String := "Hello!"
