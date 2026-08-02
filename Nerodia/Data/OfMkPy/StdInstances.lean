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
public import Nerodia.Data.PyBuffer.Basic
public import Nerodia.Data.PyBytes.Basic
public import Nerodia.Data.PyStr.Basic
public import Nerodia.Data.PyInt.Basic

/-!
# Lean ↔ Python Instances

These modules define the standard Nerodia instances used to convert Python
arguments to Lean objects and Lean returns to Python objects.
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
  if h : arg ⦂ T then
    return arg.attachType h
  else raiseArgTypeMismatch fn i arg T.toTypeExpr

/-! ## Py  -/

public instance (priority := low) [DecidablePy T] [ToTypeExpr T] : OfPyArg (Py T) T where
  ofPyArg fn i arg := private ofPyArgDecidable fn i arg

public instance : OfPyArg PyObject object where
  ofPyArg _ _ arg := private return arg

public instance : OfPyArg PyAny any where
  ofPyArg _ _ arg := private return ⟨arg.raw, by simp⟩

public instance : OfPyArg PyBuffer buffer where
  ofPyArg fn i arg := private do (← arg.getPyBuffer?).getDM do
    raiseArgTypeMismatch fn i arg buffer

public instance : MkCPyResult (Py T) T where
  mkCPyResult o := CPyBaseIO.pure o

public instance : MkPyResult (Py T) T where
  mkPyResult o := PyCResultIO.pure o

/-! ## IO -/

public instance [MkCPyResult α T] : MkCPyResult (BaseIO α) T where
  mkCPyResult x := private .ofBind x MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (IO α) T where
  mkCPyResult x := private
    .ofBind x.toBaseIO fun
    | .ok a => MkCPyResult.mkCPyResult a
    | .error e => raiseIOError e

public instance [MkCPyResult α T] : MkCPyResult (PyBaseIO α) T where
  mkCPyResult x := private x.bindCPyIO MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (PyIO α) T where
  mkCPyResult x := private x.bindCPyIO MkCPyResult.mkCPyResult

public instance [MkPyResult α T] : MkPyResult (BaseIO α) T where
  mkPyResult x := private PyBaseIO.bindPyResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (IO α) T where
  mkPyResult x := private PyIO.bindPyResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyBaseIO α) T where
  mkPyResult x := private x.bindPyResultIO MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyIO α) T where
  mkPyResult x := private x.bindPyResultIO MkPyResult.mkPyResult

/-! ## Unit -/

public instance : MkCPyResult PUnit none where
  mkCPyResult _ := getPyNone

/-! ## Empty -/

public instance : MkCPyResult Empty never where
  mkCPyResult := Empty.elim

public instance : MkCPyResult PEmpty never where
  mkCPyResult := PEmpty.elim

/-! ## String -/

public instance : OfPyArg String str where
  ofPyArg fn i arg := private PyStr.toString <$> ofPyArg fn i arg

public instance : MkCPyResult String str := ⟨mkPyStr⟩

/-! ## ByteArray -/

public instance : OfPyArg ByteArray buffer where
  ofPyArg fn i arg := private PyBuffer.getByteArray =<< ofPyArg fn i arg

-- TODO: result type (likely a `bytearray`)

/-! ## Int -/

public instance : OfPyArg Int int where
  ofPyArg fn i arg := private PyInt.toInt <$> ofPyArg fn i arg

public instance : MkCPyResult Int int := ⟨mkPyInt⟩

/-! ## Nat -/

@[extern "lean_int_to_nat"] -- in `lean.h` but no def in core
def intToNat (n : Int) (h : 0 ≤ n) : Nat :=
  n.natAbs

public instance : OfPyArg Nat int where
  ofPyArg fn i arg := private do
    let n ← ofPyArg (α := Int) fn i arg
    if h : n < 0 then
      raisePyValueError s!"{fn} argument {i} must be a nonnegative integer, got {n}"
    else
      return intToNat n (Int.le_of_not_gt h)

public instance : MkCPyResult Nat int := ⟨mkPyNat⟩

/-! ## Fin -/

public instance : OfPyArg (Fin n) int where
  ofPyArg fn i arg := private do
    let m ← ofPyArg (α := Nat) fn i arg
    if h : m < n then
      return Fin.mk m h
    else
      raisePyValueError s!"{fn} argument {i} must be less than {n}, got {m}"

public instance : MkCPyResult (Fin n) int := ⟨(mkPyNat ·)⟩
