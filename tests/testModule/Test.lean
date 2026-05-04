/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

/-- Return a greeting. -/
@[export test_greeting_for]
def greetingFor : PyMethO := .ofPyIO fun _ s => do
  if h : s.isStrInstance then
    mkPyStr s!"Hello, {PyStr.mk s h}!"
  else raisePyTypeError "argument must be str"

@[export test_init_module]
def initModule : PyModuleInit := .ofPyIO fun mod => do
  let greeting ← mkPyStr "Hello!"
  mod.addByString "greeting" greeting
