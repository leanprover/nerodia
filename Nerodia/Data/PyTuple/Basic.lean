/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
import Std.Data.Iterators

namespace Nerodia

open Classical in
/-- Returns whether {lean}`self` is an instance of {lit}`tuple`. -/
@[extern "nerodia_py_object_is_tuple_instance"]
def PyObject.isTupleInstance (self : @& PyObject) : Bool :=
  self ⦂ tuple

open PyObject in
public instance : DecidablePy tuple := private_decl%
  (Internal.decPy isTupleInstance (by simp [isTupleInstance]))

open Classical in
@[extern "nerodia_py_object_is_empty_tuple"]
def PyObject.isEmptyTuple (self : @& PyObject) : Bool :=
  self ⦂ tuple .empty

open PyObject in
public instance : DecidablePy (tuple .empty) := private_decl%
  (Internal.decPy isEmptyTuple (by simp [isEmptyTuple]))

/-- Creates a Python {lit}`tuple` object from a Lean {name}`Array` of typed Python objects. -/
@[extern "nerodia_mk_py_tuple"]
public opaque mkPyArrayTuple (xs : @& Array (Py T)) : CPyIO (PyArrayTuple T)

@[inline]
unsafe def mkPyVectorTupleImpl (xs : Vector (Py T) n) : CPyIO (PyVectorTuple T n) :=
  unsafeCast <| mkPyArrayTuple xs.toArray

/-- Creates a Python {lit}`tuple` object from a Lean {name}`Vector` of typed Python objects. -/
@[implemented_by mkPyVectorTupleImpl]
public opaque mkPyVectorTuple (xs : Vector (Py T) n) : CPyIO (PyVectorTuple T n) :=
  if h : n = 0 then
    CPyIO.pure <| cast (by rw [h]) <|
      Classical.ofNonempty (α := PyTuple (.ofTypingN T 0))
  else
    have : NonemptyPy T := ⟨xs[0]⟩
    Classical.ofNonempty

/--
Creates a Python {lit}`tuple` object from a Lean {name}`Array` of Python objects.
-/
@[extern "nerodia_mk_py_tuple"]
public def mkPyTuple (xs : @& Array PyObject) : CPyIO PyTuple :=
  mkPyArrayTuple xs |>.promote

/--
Creates a 1-element Python {lit}`tuple` object.

This is equivalent to the Python {lit}`(a,)`.
-/
@[extern "nerodia_mk_py_tuple1"]
public opaque mkPyTuple1 (a : @& Py T) : CPyIO (PyHTuple [T])

/--
Creates a 2-element Python {lit}`tuple` object.

This is equivalent to the Python {lit}`(a, b)`.
-/
@[extern "nerodia_mk_py_tuple2"]
public opaque mkPyTuple2 (a : @& Py T) (b : @& Py U) : CPyIO (PyHTuple [T, U])

open Internal in
/-- Returns a reference to the empty tuple constant (i.e., {lit}`()`). -/
@[extern "nerodia_py_environment_empty_tuple"]
public protected nonrec def PyEnvironment.emptyTuple (env : @& PyEnvironment) : PyEmptyTuple :=
  env.emptyTupleCore

/-- Returns the empty tuple constant of the Python environment (i.e. {lit}`()`).-/
@[extern "nerodia_get_py_empty_tuple"]
public def getPyEmptyTuple : CPyBaseIO PyEmptyTuple :=
  PyBaseIO.toCPyBaseIO do (·.emptyTuple) <$> getPyEnvironment

namespace PyTuple

open Internal Nerodia in
/-- Returns the elements of {lean}`self` as a Lean {lean}`Array`. -/
-- This function is pure because the tuple data of instances of `tuple` is immutable.
@[extern "nerodia_py_tuple_to_array"]
public def toArray (self : @& PyTuple) : Array PyObject :=
  self.toArrayCore

/-- Returns the number of elements in {lean}`self` as a Lean {name}`USize`. -/
-- This function is pure because the tuple data of instances of `tuple` is immutable.
@[extern "nerodia_py_tuple_usize"]
public def usize (self : @& PyTuple) : USize :=
  self.toArray.usize

@[simp, grind =]
public theorem usize_eq : usize xs = xs.toArray.usize := by rfl

@[inline] public def sizeImpl (self : @& PyTuple) : Nat :=
  self.usize.toNat

/-- Returns the number of elements in {lean}`self` as a Lean {name}`Nat`. -/
@[implemented_by sizeImpl]
public def size (self : @& PyTuple) : Nat :=
  self.toArray.size

@[simp, grind =]
public theorem size_eq : size xs = xs.toArray.size := by rfl

end PyTuple
