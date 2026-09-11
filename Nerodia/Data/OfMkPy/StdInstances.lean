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
public import Nerodia.Data.PyBool.Basic
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
  mkPyResult x := private PyBaseIO.bindPyCResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (IO α) T where
  mkPyResult x := private PyIO.bindPyCResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyBaseIO α) T where
  mkPyResult x := private x.bindPyCResultIO MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyIO α) T where
  mkPyResult x := private x.bindPyCResultIO MkPyResult.mkPyResult

/-! ## Unit -/

public instance : MkCPyResult PUnit none where
  mkCPyResult _ := getPyNone

/-! ## Empty -/

public instance : MkCPyResult Empty never where
  mkCPyResult := Empty.elim

public instance : MkCPyResult PEmpty never where
  mkCPyResult := PEmpty.elim

/-! ## Option -/

public instance [OfPyArg α T] : OfPyArg (Option α) (.optional T) where
  ofPyArg fn i arg := private
    if arg ⦂ none then return none
    else return some (← ofPyArg fn i arg)

public instance [MkCPyResult α T] : MkCPyResult (Option α) (.optional T) where
  mkCPyResult a? := private match a? with
    | none => getPyNone.toCPyIO.promote
    | some a => MkCPyResult.mkCPyResult a |>.promote

public instance [MkPyResult α T] : MkPyResult (Option α) (.optional T) where
  mkPyResult a? := private match a? with
    | none => getPyNone.toCPyIO.toPyCResultIO.promote
    | some a => MkPyResult.mkPyResult a |>.promote

/-! ## Bool -/

public instance : OfPyArg Bool bool where
  ofPyArg fn i arg := private PyBool.toBool <$> ofPyArg fn i arg

public instance : MkCPyResult Bool bool := ⟨(mkPyBool ·)⟩

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

public instance : OfPyArg Nat int where
  ofPyArg fn i arg := private do
    let n ← ofPyArg (α := PyInt) fn i arg
    n.toNat?.getDM do
      raisePyValueError s!"{fn} argument {i} must be a nonnegative integer, got {n}"

public instance : MkCPyResult Nat int := ⟨mkPyNat⟩

/-! ## Fin -/

public instance : OfPyArg (Fin n) int where
  ofPyArg fn i arg := private do
    let m ← ofPyArg (α := Nat) fn i arg
    if h : m < n then
      return Fin.mk m h
    else
      raisePyValueError s!"{fn} argument {i} must be less than {n}, got {m}"

public instance : MkCPyResult (Fin n) int := ⟨mkPyFin⟩

/-! ## Fixed-Width Integers -/

@[inline] def ofPyArgInt?
  (fn : String) (i : Nat) (arg : PyObject)
  (what : String) (f : PyInt → Option α)
: PyIO α := do
  let n ← ofPyArg (α := PyInt) fn i arg
  (f n).getDM <| raisePyValueError s!"{fn} argument {i} \
    must fit within {what}, got {n}"

public instance : OfPyArg ISize int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a signed word" (·.toISize?)

public instance : MkCPyResult ISize int := ⟨mkPyISize⟩

public instance : OfPyArg USize int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "an unsigned word" (·.toUSize?)

public instance : MkCPyResult USize int := ⟨mkPyUSize⟩

public instance : OfPyArg Int64 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 64-bit signed integer" (·.toInt64?)

public instance : MkCPyResult Int64 int := ⟨mkPyInt64⟩

public instance : OfPyArg UInt64 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 64-bit unsigned integer" (·.toUInt64?)

public instance : MkCPyResult UInt64 int := ⟨mkPyUInt64⟩

public instance : OfPyArg Int32 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 32-bit signed integer" (·.toInt32?)

public instance : MkCPyResult Int32 int := ⟨mkPyInt32⟩

public instance : OfPyArg UInt32 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 32-bit unsigned integer" (·.toUInt32?)

public instance : MkCPyResult UInt32 int := ⟨mkPyUInt32⟩

public instance : OfPyArg Int16 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 16-bit signed integer" (·.toInt16?)

public instance : MkCPyResult Int16 int := ⟨mkPyInt16⟩

public instance : OfPyArg UInt16 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "a 16-bit unsigned integer" (·.toUInt16?)

public instance : MkCPyResult UInt16 int := ⟨mkPyUInt16⟩

public instance : OfPyArg Int8 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "an 8-bit signed integer" (·.toInt8?)

public instance : MkCPyResult Int8 int := ⟨mkPyInt8⟩

public instance : OfPyArg UInt8 int where
  ofPyArg fn i arg := private ofPyArgInt? fn i arg "an 8-bit unsigned integer" (·.toUInt8?)

public instance : MkCPyResult UInt8 int := ⟨mkPyUInt8⟩
