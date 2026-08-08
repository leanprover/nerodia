/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

open Nerodia

/-- info: 0 -/
#guard_msgs in #eval mkPyNat 0 -- base case
/-- info: 0 -/
#guard_msgs in #eval mkPyInt 0
/-- info: -1 -/
#guard_msgs in #eval mkPyInt (-1)
/-- info: 13 -/
#guard_msgs in #eval mkPyNat 13 -- one byte
/-- info: 13 -/
#guard_msgs in #eval mkPyInt 13
/-- info: -13 -/
#guard_msgs in #eval mkPyInt (-13)
/-- info: 420 -/
#guard_msgs in #eval mkPyNat 420 -- multi-byte
/-- info: 420 -/
#guard_msgs in #eval mkPyInt 420
/-- info: -420 -/
#guard_msgs in #eval mkPyInt (-420)
/-- info: 9223372036854775808 -/
#guard_msgs in #eval mkPyNat (2^63) -- big scalar / negative MSB
/-- info: 9223372036854775808 -/
#guard_msgs in #eval mkPyInt (2^63)
/-- info: -9223372036854775808 -/
#guard_msgs in #eval mkPyInt (-(2^63))
/-- info: 18446744073709551616 -/
#guard_msgs in #eval mkPyNat (2^64) -- big non-scalar / positive MSB
/-- info: 18446744073709551616 -/
#guard_msgs in #eval mkPyInt (2^64)
/-- info: -18446744073709551616 -/
#guard_msgs in #eval mkPyInt (-(2^64))

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
[119, 111, 119]
wow
-/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← mkPyBytes (.mk #[119, 111, 119])
  IO.println bytes.size
  IO.println bytes.usize
  IO.println bytes.toByteArray
  IO.println (← bytes.getByteArray)
  let str ← bytes.decodeUTF8
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

/-- info: "��" -/
#guard_msgs in
#eval PyIO.toIO do
  let bytes ← mkPyBytes (.mk #[0xED, 0xA0, 0x80, 0xED, 0xA0, 0xBD])
  let str ← bytes.decode .utf8 .surrogatePass
  -- Adjacent lone surrogates must not merge: one `�` per surrogate keeps
  -- Lean and Python string lengths in agreement.
  return str.toString

/-- info: b'\x00' -/
#guard_msgs in
#eval PyIO.toIO do (← (← mkPyBytes <| .mk #[0]).bytes).repr

/-- error: TypeError: cannot convert 'int' object to bytes -/
#guard_msgs in
#eval PyIO.toIO do (← (← mkPyInt 0).bytes).repr

/-- info: 10 -/
#guard_msgs in
#eval PyIO.toIO do (← (← mkPyStr "10").int).repr

/-- error: TypeError: 'str' object cannot be interpreted as an integer -/
#guard_msgs in
#eval PyIO.toIO do (← (← mkPyStr "10").index).repr

/-- info: 0 -/
#guard_msgs in
#eval PyIO.toIO do (← (← mkPyInt 0).index).repr

/-- info: hello; <not a str> -/
#guard_msgs in
#eval PyIO.toIO do
  let fn (o : PyObject) : PyIO String := do
    if h : o ⦂ str then
      let o := o.attachType h
      return o.toString
    else
      return "<not a str>"
  IO.print <| ← fn (← mkPyStr "hello")
  IO.print "; "
  IO.print <| ← fn (← mkPyInt 3)

/-- info: None -/
#guard_msgs in
#eval PyIO.toIO do (← getPyNone).repr

open Internal Nerodia in
/-- error: SystemError: no exception was set -/
#guard_msgs in
#eval PyIO.failureUnsafe (α := Empty)

-- Verify `CPyUnitIO.ok` error check (previously broken)
#guard_msgs in #eval CPyUnitIO.ok.toPyIO

/-- error: AttributeError: module 'sys' has no attribute 'bogus' -/
#guard_msgs in
#eval PyIO.toIO do
  let sys ← Nerodia.import "sys"
  let val ← sys.getAttrByString "bogus"
  val.str

/-- error: EOFError -/
#guard_msgs in
#eval raisePyEOFError (α := Empty)

/-- error: RuntimeError: my error -/
#guard_msgs in
#eval PyIO.toIO (α := Empty) <| IO.toPyIO do throw (IO.userError "my error")
