/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.CPyIO

/-!
# Python-to-Lean Arguments

This module define the type class used
to convert Pyton arguments to Lean objects.

This class is used by the by the Nerodia compiler attribute
{lit}`@[py_module_fn]`.
-/

namespace Nerodia

/-- Type class used to construct a Lean object from a Python function argument. -/
public class OfPyArg (α : Type) (T : outParam TypePred) where
  ofPyArg (fn : String) (i : Nat) (arg : PyObject) : PyIO α
