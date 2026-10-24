/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO

/-!
# Python Float Basics

This module contains definitions for converting Python floats to/from
Lean types.
-/

namespace Nerodia

open Classical in
/-- Returns whether {lean}`self` is an instance of {lit}`float`. -/
@[extern "nerodia_py_object_is_float_instance"]
def PyObject.isFloatInstance (self : @& PyObject) : Bool :=
  self ⦂ float

open PyObject in
public instance : DecidablePy float := private_decl%
  (Internal.decPy isFloatInstance (by simp [isFloatInstance]))

/-- Creates a Python float from a 64-bit Lean float. -/
@[extern "nerodia_mk_py_float"]
public opaque mkPyFloat (x : Float) : CPyIO PyFloat

/-- Creates a Python float from a 32-bit Lean float. -/
@[inline] public def mkPyFloat32 (x : Float32) : CPyIO PyFloat :=
  mkPyFloat x.toFloat

namespace PyFloat

/-- Returns the value of {lean}`self` as a Lean {lean}`Float`. -/
-- This function is pure because the float value of instances of `float` is immutable.
@[extern "nerodia_py_float_to_float"]
public opaque toFloat (self : @& PyFloat) : Float

/-- Returns the value of {lean}`self` as a Lean {lean}`Float32`. -/
@[inline] public def toFloat32 (self : @& PyFloat) : Float32 :=
  self.toFloat.toFloat32

@[inline] public protected def toString (self : PyFloat) : String :=
  toString self.toFloat

public instance : ToString PyFloat := ⟨PyFloat.toString⟩
