/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

namespace Nerodia

/-- An identifier of a Python type constant (e.g., {lean}`"str"`). -/
public structure TypeConst where
  ofString ::
    protected toString : String
    deriving Nonempty, DecidableEq

public instance : ToString TypeConst := ⟨TypeConst.toString⟩

/-- A Python type expression. -/
public structure TypeExpr where
  ofString ::
    protected toString : String
    deriving Nonempty, DecidableEq

namespace TypeExpr

public instance : ToString TypeExpr := ⟨TypeExpr.toString⟩

@[inline, expose] public def ofTypeConst (n : TypeConst) : TypeExpr :=
  ⟨n.toString⟩

public instance : Coe TypeConst TypeExpr := ⟨ofTypeConst⟩
