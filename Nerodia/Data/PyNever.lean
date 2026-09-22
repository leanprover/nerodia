/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Py.Basic

/-! # PyNever -/

namespace Nerodia

/--
The special form [{lit}`Never`][1], which is the {lean}`Empty` of Python.

[1]: https://typing.python.org/en/latest/spec/special-types.html#never
-/
public opaque never : Constant

/-- Python {lit}`Never`. The bottom (⊥) element of the set of typings. -/
public def Typing.never : Typing :=
  ofFn fun _ => False

public instance : CoeDep Constant never Typing := ⟨.never⟩

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.never : TypeExpr :=
  ⟨"Never"⟩

public instance : CoeDep Constant never TypeExpr := ⟨.never⟩
public instance : ToTypeExpr never := ⟨never⟩

@[simp, grind .] public theorem PyObject.HasType.not_never : ¬ o ⦂ never := by
  simp [Typing.never]

@[deprecated PyObject.HasType.not_never (since := "2026-09-22")]
public abbrev Typing.not_hasType_never := @PyObject.HasType.not_never

public instance : DecidablePy never := private_decl%
  fun _ => isFalse PyObject.HasType.not_never

/--
An instance of the empty type [{lit}`Never`][1]. There are no inhabitants.

[1]: https://docs.python.org/3/library/typing.html#typing.Never
-/
public abbrev PyNever := Py never

public instance : ViewPy never PyNever := ⟨rfl⟩

/-- Anything holds from an instance of the empty type (c.f., {lean}`Empty.elim`). -/
@[macro_inline, irreducible, expose] -- for codegen
public def PyNever.elim {α : Sort u} (self : PyNever) : α :=
  self.toPyObject_hasType.not_never.elim
