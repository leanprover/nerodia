/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia

open Nerodia

/-- info: "hello" -/
#guard_msgs in
#eval PyIO.toIO do
  return (← mkPyStr "hello").toString

/-- info: some "hello"  -/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← (← mkPyStr "hello").utf8Encode
  return String.fromUTF8? bytes.toByteArray

/-- info: "None" -/
#guard_msgs in
#eval PyIO.toIO do
  return (← (← getPyContext).none.repr).toString

/-- error: SystemError: C FFI returned NULL without setting an exception -/
#guard_msgs in
#eval (unsafeCast (pure CPtr.null : BaseIO (CPtr Empty)) : CPyIO Empty)

/-- error: AttributeError: module 'sys' has no attribute 'bogus' -/
#guard_msgs in
#eval PyIO.toIO do
  let sys ← Nerodia.import "sys"
  let val ← sys.getAttrByString "bogus"
  val.str
