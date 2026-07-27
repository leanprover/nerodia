/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
-- classes
public import Nerodia.Data.OfMkPy.OfPyArg
public import Nerodia.Data.OfMkPy.MkPyResult
-- utilities
public import Nerodia.Data.PyObject.Basic
public import Nerodia.Data.Exceptions
public import Nerodia.Data.PyType.Basic
-- interface types
public import Nerodia.Data.PyNone.Basic
public import Nerodia.Data.PyStr.Basic
public import Nerodia.Data.PyInt.Basic

/-!
# Lean ↔ Python Instances

These module defines the standard Nerodia instances used to convert Python
argumens to Lean objects and Lean returns to Pyton objects.
-/

namespace Nerodia

open OfPyArg (ofPyArg)

@[inline] def raiseArgTypeMismatch
  (fn : String) (i : Nat) (arg : PyObject) (expected : TypeExpr)
: PyIO α := do
  let actual ← (← arg.getType).getQualName
  raisePyTypeError s!"{fn} argument {i} must be {expected}, got {actual}"

@[inline] def ofPyArgDecidable
  [DecidablePy T] [ToTypeExpr T]
  (fn : String) (i : Nat) (arg : PyObject)
: PyIO (Py T) := do
  if h : arg.raw ∈ T then
    return Py.mk arg.raw h
  else raiseArgTypeMismatch fn i arg (ToTypeExpr.toTypeExpr T)

/-! ## Py  -/

public instance (priority := low) [DecidablePy T] [ToTypeExpr T] : OfPyArg (Py T) T where
  ofPyArg fn i arg := private ofPyArgDecidable fn i arg

public instance : OfPyArg PyObject object where
  ofPyArg _ _ arg := private return PyObject.mk arg.raw

public instance : OfPyArg PyAny any where
  ofPyArg _ _ arg := private return ⟨arg.raw, by simp⟩

public instance : MkCPyResult (Py T) T where
  mkCPyResult o := CPyBaseIO.pure o

public instance : MkPyResult (Py T) T where
  mkPyResult o := PyCResultIO.pure o

/-! ## IO -/

public instance [MkCPyResult α T] : MkCPyResult (BaseIO α) T where
  mkCPyResult x := .ofBind x MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (PyBaseIO α) T where
  mkCPyResult x := x.bindCPyIO MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (PyIO α) T where
  mkCPyResult x := x.bindCPyIO MkCPyResult.mkCPyResult

public instance [MkPyResult α T] : MkPyResult (BaseIO α) T where
  mkPyResult x := PyBaseIO.bindPyResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyBaseIO α) T where
  mkPyResult x := x.bindPyResultIO MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyIO α) T where
  mkPyResult x := x.bindPyResultIO MkPyResult.mkPyResult

/-! ## Unit -/

public instance : MkCPyResult PUnit .none where
  mkCPyResult _ := getPyNone

/-! ## String -/

public instance : OfPyArg String str where
  ofPyArg fn i arg := private PyStr.toString <$> ofPyArg fn i arg

public instance : MkCPyResult String str := ⟨mkPyStr⟩

/-! ## Int -/

public instance : OfPyArg Int int where
  ofPyArg fn i arg := private PyInt.toInt <$> ofPyArg fn i arg

public instance : MkCPyResult Int int := ⟨mkPyInt⟩
