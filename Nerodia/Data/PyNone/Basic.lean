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
@[extern "nerodia_py_object_is_none", view_method,
deprecated "Use `self ⦂ none` instead." (since := "2026-09-11")]
public def PyObject.isNone (self : @& PyObject) : Bool :=
  self ⦂ none

@[grind _=_, deprecated "Deprecated with `isNone`." (since := "2026-09-11")]
public theorem PyObject.isNone_iff_hasType : isNone o ↔ o ⦂ none := by
  simp [PyObject.isNone]

open PyObject in
set_option linter.deprecated false in
public instance : DecidablePy none := private_decl%
  (Internal.decPy isNone fun _ => isNone_iff_hasType)

@[simp, deprecated "Deprecated with `isNone`." (since := "2026-09-11")]
public theorem PyNone.isNone_eq_true : (o : PyNone).isNone = true := by
  simp [PyObject.isNone_iff_hasType]

open Internal in
/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_py_environment_none"]
public protected nonrec def PyEnvironment.none (env : @& PyEnvironment) : PyNone :=
  env.noneCore

/-- Returns the {lit}`None` constant of the Python environment. -/
@[extern "nerodia_get_py_none"]
public def getPyNone : CPyBaseIO PyNone :=
  PyBaseIO.toCPyBaseIO do (·.none) <$> getPyEnvironment
