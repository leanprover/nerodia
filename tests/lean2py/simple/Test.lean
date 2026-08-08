/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia

open Nerodia

/-- A Lean-to-Python test module. -/
py_module "testmodule"

/-- Add two integers using Lean. -/
@[py_module_fn "my_add"]
def myAdd (a b : Int) : Int :=
  a + b

@[py_module_fn]
def addBit (a : Nat) (b : Fin 2) : Nat :=
  a + b

@[py_module_fn]
def alwaysRaise : IO Empty :=
  throw <| IO.userError "alwaysRaise() called"

@[py_module_fn]
def countbytes (bs : ByteArray) : Nat :=
  bs.size

/-- Return a standard greeting ("Olá!"). -/
@[py_module_fn]
def greet : String :=
  s!"Olá!"

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
unsafe def setUser (s : String := "default") : BaseIO Unit := do
  userRef.set s

/-- Returns a greeting for the current user. -/
@[py_module_fn]
def greetUser : BaseIO String := do
  return s!"Hello, {← userRef.get}!"
