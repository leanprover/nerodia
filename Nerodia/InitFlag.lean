/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import all Lean.ImportingFlag

namespace Nerodia

@[export nerodia_internal_set_init]
def setInit (init : Bool) : BaseIO Unit := do
  Lean.importingRef.set init
