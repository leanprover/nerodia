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
public class MkCResult (α : Type u) (T : outParam TypePred) where
  mkCResult : α → CPyIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkCResult {α} {T} [MkCResult α T] (a : α) : CPyIO Py.Raw :=
  MkCResult.mkCResult a |>.raw

public instance : MkCResult (Py T) T where
  mkCResult o := CPyBaseIO.pure o

public instance [MkCResult α T] : MkCResult (BaseIO α) T where
  mkCResult x := .ofBind x MkCResult.mkCResult

public instance [MkCResult α T] : MkCResult (PyBaseIO α) T where
  mkCResult x := x.bindCPyIO MkCResult.mkCResult

public instance [MkCResult α T] : MkCResult (PyIO α) T where
  mkCResult x := x.bindCPyIO MkCResult.mkCResult

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]`.
-/
public class MkResult (α : Type u) (T : outParam TypePred) where
  mkResult : α → PyResultIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.mkResult {α} {T} [MkResult α T] (a : α) : PyResultIO Py.Raw :=
  MkResult.mkResult a |>.raw

public instance (priority := low) [MkCResult α T] : MkResult α T where
  mkResult x := CPyIO.toPyResultIO (MkCResult.mkCResult x)

public instance (priority := low) [MkResult α T] : MkCResult α T where
  mkCResult x := PyResultIO.toCPyIO (MkResult.mkResult x)

public instance : MkResult (Py T) T where
  mkResult o := PyResultIO.pure o

public instance [MkResult α T] : MkResult (BaseIO α) T where
  mkResult x := PyBaseIO.bindPyResultIO x MkResult.mkResult

public instance [MkResult α T] : MkResult (PyBaseIO α) T where
  mkResult x := x.bindPyResultIO MkResult.mkResult

public instance [MkResult α T] : MkResult (PyIO α) T where
  mkResult x := x.bindPyResultIO MkResult.mkResult
