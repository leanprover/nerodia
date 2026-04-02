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
#eval id (α := PyIO _) do
  return (← mkPyStrObject "hello").toString

/-- info: some "hello"  -/
#guard_msgs in
#eval id (α := PyIO _) do
  let bytes ← (← mkPyStrObject "hello").utf8Encode
  return String.fromUTF8? bytes.toByteArray

/-- info: "None" -/
#guard_msgs in
#eval id (α := PyIO _) do
  return (← (← getPyContext).none.repr).toString
