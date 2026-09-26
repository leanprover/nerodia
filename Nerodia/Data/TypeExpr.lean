/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

namespace Nerodia

/-- A Python type expression. -/
public structure TypeExpr where
  ofString ::
    protected toString : String
    deriving Nonempty, DecidableEq

public instance : ToString TypeExpr := ⟨TypeExpr.toString⟩

namespace TypeExpr

/-
`@[irreducible]` keeps these definitions from being expanded during `whnf`
in the Nerodia compiler when the definitions are imported into a non-module
-/

@[inline, irreducible] public def union (lhs rhs : TypeExpr) : TypeExpr :=
  ⟨s!"{lhs} | {rhs}"⟩ -- equivalent to `Union[<lhs>, <rhs>]`

@[inline, irreducible] public def optional (expr : TypeExpr) : TypeExpr :=
  ⟨s!"{expr} | None"⟩ -- equivalent to `Optional[<expr>]`
