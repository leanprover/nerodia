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
@[py_module_fn "greeting_for" (sig := "(s: str, /) -> str")]
def greetingFor : PyMethO := .ofPyIO fun _ s => do
  if h : s.isStrInstance then
    mkPyStr s!"Hello, {PyStr.mk s h}!"
  else raisePyTypeError "argument must be str"

@[py_module_init]
def initModule : PyModuleInit := .ofPyIO fun mod => do
  let greeting ← mkPyStr "Hello!"
  mod.addByString "greeting" greeting
