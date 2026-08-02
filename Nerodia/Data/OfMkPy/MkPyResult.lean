/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.CPyIO

/-!
# Lean-to-Python Returns

These modules define the type classes used to
convert Lean returns to Python objects.

These classes are used by the Nerodia compiler attributes
{lit}`@[py_module_fn]` and {lit}`@[py_module_attr]`.
-/

namespace Nerodia

/-! ## Type Classes -/

/-- Type class used to construct Python return values from Lean objects. -/
public class MkPyResult (α : Type u) (T : outParam Typing) where
  mkPyResult : α → PyCResultIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.mkPyResult {α} {T} [MkPyResult α T] (a : α) : PyCResultIO Py.Raw :=
  MkPyResult.mkPyResult a |>.raw

/--
Type class used to construct Python return values from Lean objects.

An optimized version of {lean}`MkPyResult` used when the created Python
object is directly available via {lean}`CPyIO`.
-/
public class MkCPyResult (α : Type u) (T : outParam Typing) where
  mkCPyResult : α → CPyIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkCPyResult {α} {T} [MkCPyResult α T] (a : α) : CPyIO Py.Raw :=
  MkCPyResult.mkCPyResult a |>.raw

/-! ## Interlink -/

public instance (priority := low) [MkCPyResult α T] : MkPyResult α T where
  mkPyResult x := CPyIO.toPyResultIO (MkCPyResult.mkCPyResult x)

public instance (priority := low) [MkPyResult α T] : MkCPyResult α T where
  mkCPyResult x := PyCResultIO.toCPyIO (MkPyResult.mkPyResult x)
