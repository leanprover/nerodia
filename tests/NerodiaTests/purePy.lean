/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia
import Nerodia.Test.Pure

open Nerodia

/-- info: None -/
#guard_msgs in #eval pyNone.repr

/-- info: true -/
#guard_msgs in #eval pyNone ⦂ none
