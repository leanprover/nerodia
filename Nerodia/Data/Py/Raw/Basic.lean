/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Py.Raw.Type

namespace Nerodia.Py.Raw

open Internal in
/-- Returns the address of the Python object (not the Lean wrapper). -/
@[extern "nerodia_py_object_addr"]
public def addr (self : @& Py.Raw) : Addr :=
  self.toModel.addr
