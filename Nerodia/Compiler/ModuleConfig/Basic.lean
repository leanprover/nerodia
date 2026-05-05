/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Neordiac Module Configuration -/

open Lean

namespace Nerodia

public structure ModuleConfig where
  name : String
  doc? : Option String := none
  init? : Option String := none
  deriving Inhabited
