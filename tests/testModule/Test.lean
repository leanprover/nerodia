/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

/-- A Lean-to-Python test module. -/
py_module "testmodule"

/-- Return a standard greeting. -/
@[py_module_fn]
def greet : String :=
  s!"Hello!"

/-- Return a greeting. -/
@[py_module_fn "greeting_for"]
def greetingFor (s : String) : String :=
  s!"Hello, {s}!"

/-- Return a greeting for two entities. -/
@[py_module_fn]
def greet2 (a b : String) : String :=
  s!"Hello, {a} and {b}!"

/-- The standard greeting. -/
@[py_module_attr]
def greeting : String := "Hello!"

initialize userRef : IO.Ref String ← IO.mkRef "anonymous"

/-- Sets the current user. -/
@[py_module_fn]
def setUser (s : String) : BaseIO Unit := do
  userRef.set s

/-- Returns a greeting for the current user. -/
@[py_module_fn]
def greetUser : BaseIO String := do
  return s!"Hello, {← userRef.get}!"
