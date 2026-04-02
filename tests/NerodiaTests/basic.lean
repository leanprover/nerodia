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
#eval id (α := EPyM _) do
  (← Nerodia.mkString "hello").getString

/-- info: some "hello"  -/
#guard_msgs in
#eval id (α := EPyM _) do
  let bytes ← (← Nerodia.mkString "hello").decodeUtf8
  return String.fromUTF8? bytes.toByteArray

/-- info: "None" -/
#guard_msgs in
#eval id (α := EPyM _) do
  (← (← getPyContext).none.repr).getString
