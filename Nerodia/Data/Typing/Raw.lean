/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.TypeExpr
public import Nerodia.Data.Py.Raw.Type

/-! # Typings -/

namespace Nerodia

/--
A typing predicate for Python objects.

This is the propositional equivalent of a Python type expression.
However, it can express more complex types (e.g., intersections) than Python's
base type system and is thus closer in power to the type system of Python's
more advanced type checkers (e.g., [{lit}`ty`][1]).

[1]: https://github.com/astral-sh/ty
-/
@[irreducible, expose] -- for codegen
public def Typing : Type :=
  Internal.Py.Raw → Prop

/--
Associates a Python type expression with a Nerodia type predicate.

This class is used by the Nerodia compiler to generate Python type annotations.
For this to work, all instances must be publicly reducible to {lean}`String`.
Thus, definitions they use must be marked {attr}`@[expose]`.
-/
public class ToTypeExpr (T : Typing) where
  toTypeExpr : TypeExpr

namespace Typing
export ToTypeExpr (toTypeExpr)
end Typing

/--
Auxiliary type used for values representing a static Python constant.

Similar to {lean}`Lean.Parser.Category`, definitions of this type have no
content, they simply reserve names that can be coerced into other types (e.g.,
{lean}`TypeExpr` or {lean}`Typing`) via {lean}`CoeDep`.

**Users of Nerodia should not define values of this type themselves.**
-/
public structure Constant where
  private mk ::
    private val : NonScalar
    deriving Inhabited

unseal Typing in
public def Internal.Py.Raw.HasType (T : Typing) (o : Py.Raw) : Prop :=
  T o

unseal Typing in
public theorem Internal.Py.Raw.HasType.ext
  {T U : Typing} (h : ∀ o, HasType T o ↔ HasType U o) : T = U
:= funext fun o => propext (h o)

@[deprecated "Use `PyObject.HasType` or `o ⦂ T` instead."  (since := "2026-09-19")]
public protected abbrev Typing.HasType (T : Typing) (o : Internal.Py.Raw) : Prop :=
  o.HasType T

export Typing (HasType)

unseal Typing in
public def Internal.Nerodia.Typing.ofRawFn (p : Py.Raw → Prop) : Typing :=
  p

unseal Typing in
open Internal in
public theorem Internal.Py.Raw.HasType.ofRawFn_iff :
  HasType (.ofRawFn p) o ↔ p o
:= Iff.intro id id

/-! ## object -/

/--
The ultimate Python base class, [{lit}`object`][1].

[1]: https://docs.python.org/3/library/functions.html#object
-/
public opaque object : Constant

open Internal in
/-- Python {lit}`object`. The top (⊤) element of the set of typings. -/
public def Typing.object : Typing :=
  .ofRawFn fun _ => True

public instance : CoeDep Constant object Typing := ⟨.object⟩

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.object : TypeExpr :=
  ⟨"object"⟩

public instance : CoeDep Constant object TypeExpr := ⟨.object⟩
public instance : ToTypeExpr object := ⟨object⟩

open Internal Nerodia in
public theorem Internal.Py.Raw.HasType.object : HasType .object o := by
  simp [Typing.object, Typing.ofRawFn, HasType]
