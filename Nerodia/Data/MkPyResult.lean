/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.CPyIO

/-!
# Pythom Export Types

This module defines the types of functions exported from Lean to C for Python.
-/

namespace Nerodia

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]`.
-/
public class MkCPyResult (α : Type u) (T : outParam TypePred) where
  mkCPyResult : α → CPyIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkCPyResult {α} {T} [MkCPyResult α T] (a : α) : CPyIO Py.Raw :=
  MkCPyResult.mkCPyResult a |>.raw

public instance : MkCPyResult (Py T) T where
  mkCPyResult o := CPyBaseIO.pure o

public instance [MkCPyResult α T] : MkCPyResult (BaseIO α) T where
  mkCPyResult x := .ofBind x MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (PyBaseIO α) T where
  mkCPyResult x := x.bindCPyIO MkCPyResult.mkCPyResult

public instance [MkCPyResult α T] : MkCPyResult (PyIO α) T where
  mkCPyResult x := x.bindCPyIO MkCPyResult.mkCPyResult

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]`.
-/
public class MkPyResult (α : Type u) (T : outParam TypePred) where
  mkPyResult : α → PyResultIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.mkPyResult {α} {T} [MkPyResult α T] (a : α) : PyResultIO Py.Raw :=
  MkPyResult.mkPyResult a |>.raw

public instance (priority := low) [MkCPyResult α T] : MkPyResult α T where
  mkPyResult x := CPyIO.toPyResultIO (MkCPyResult.mkCPyResult x)

public instance (priority := low) [MkPyResult α T] : MkCPyResult α T where
  mkCPyResult x := PyResultIO.toCPyIO (MkPyResult.mkPyResult x)

public instance : MkPyResult (Py T) T where
  mkPyResult o := PyResultIO.pure o

public instance [MkPyResult α T] : MkPyResult (BaseIO α) T where
  mkPyResult x := PyBaseIO.bindPyResultIO x MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyBaseIO α) T where
  mkPyResult x := x.bindPyResultIO MkPyResult.mkPyResult

public instance [MkPyResult α T] : MkPyResult (PyIO α) T where
  mkPyResult x := x.bindPyResultIO MkPyResult.mkPyResult
