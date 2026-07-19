/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.CPyIO

namespace Nerodia

@[extern "nerodia_mk_py_type_error"]
opaque mkPyTypeError (msg : @& String) : CPyIO PyTypeError

/-- Raises a {lean}`PyTypeError` with the given message {lean}`msg`. -/
@[inline] public def raisePyTypeError (msg : String) : CPyIO α :=
  Internal.raiseNew <| (mkPyTypeError msg).cast .inter_left
