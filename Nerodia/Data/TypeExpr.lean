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
