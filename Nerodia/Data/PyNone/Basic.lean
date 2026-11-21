/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.Internal.ViewMethod

namespace Nerodia

open Classical in
/-- Equivalent to the Python {lit}`self is None`. -/
@[extern "nerodia_py_object_is_none"]
def PyObject.isNone (self : @& PyObject) : Bool :=
  self ⦂ none

theorem PyObject.isNone_iff_hasType : isNone o ↔ o ⦂ none := by
  simp [PyObject.isNone]

open PyObject in
public instance : DecidablePy none := private_decl%
  (Internal.decPy isNone fun _ => isNone_iff_hasType)

public instance [DecidablePy T] : DecidablePy (.optional T) := private_decl%
  fun x => decidable_of_iff' (x ⦂ T ∪ none) <| by rw [Typing.optional_eq_union_none]

open Internal in
/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_py_environment_none"]
public protected nonrec def PyEnvironment.none (env : @& PyEnvironment) : PyNone :=
  env.noneCore

/-- Returns the {lit}`None` constant of the Python environment. -/
@[extern "nerodia_get_py_none"]
public def getPyNone : CPyBaseIO PyNone :=
  PyBaseIO.toCPyBaseIO do (·.none) <$> getPyEnvironment
