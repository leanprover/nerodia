/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

/-- info: "hello" -/
#guard_msgs in
#eval PyIO.toIO do
  return (← mkPyStr "hello").toString

/-- info: some "hello"  -/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← (← mkPyStr "hello").encodeUTF8
  return String.fromUTF8? bytes.toByteArray

/--
info: 3
3
[119, 111, 119]
wow
-/
#guard_msgs in
#eval do
  let bytes ← PyIO.toIO do
    mkPyBytes (.mk #[119, 111, 119])
  IO.println bytes.size
  IO.println bytes.usize
  IO.println bytes.toByteArray
  let str ← PyIO.toIO do
    bytes.decodeUTF8
  IO.println str

/-- info: [237, 160, 128] -/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← mkPyBytes (.mk #[0xED, 0xA0, 0x80])
  let str ← bytes.decode .utf8 .surrogatePass
  let roundtrip ← str.encode .utf8 .surrogatePass
  return roundtrip.toByteArray

/-- info: "�" -/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← mkPyBytes (.mk #[0xED, 0xA0, 0x80])
  let str ← bytes.decode .utf8 .surrogatePass
  -- Test that `toString` handles lone surrogates
  return str.toString

/-- info: None -/
#guard_msgs in
#eval PyIO.toIO do (← getPyNone).repr

/-- error: SystemError: no exception was set -/
#guard_msgs in
#eval PyIO.failureUnsafe (α := Empty)

/-- error: AttributeError: module 'sys' has no attribute 'bogus' -/
#guard_msgs in
#eval PyIO.toIO do
  let sys ← Nerodia.import "sys"
  let val ← sys.getAttrByString "bogus"
  val.str

/-- error: EOFError -/
#guard_msgs in
#eval raisePyEOFError (α := Empty)
