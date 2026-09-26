/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia
-- Avoids Python initialize/finalize on each `#eval`
import Nerodia.Test.Pure

/-! # PyInt Tests -/

open Nerodia

/-! ## Lean <-> Python Integer Conversion Roundtrip -/

/-- info: 0 -/
#guard_msgs in #eval mkPyNat 0 -- base case
/-- info: 0 -/
#guard_msgs in #eval mkPyInt 0
/-- info: -1 -/
#guard_msgs in #eval mkPyInt (-1)

def testConvert (n : Nat) : PyIO (Array PyInt) := do
  return #[← mkPyNat n, ← mkPyInt n, ← mkPyInt (-n)]

/-- info: #[13, 13, -13] -/
#guard_msgs in #eval testConvert 13 -- one byte
/-- info: #[420, 420, -420] -/
#guard_msgs in #eval testConvert 420 -- multi-byte
/-- info: #[9223372036854775808, 9223372036854775808, -9223372036854775808] -/
#guard_msgs in #eval testConvert (2^63) -- big scalar / negative MSB
/-- info: #[18446744073709551616, 18446744073709551616, -18446744073709551616] -/
#guard_msgs in #eval testConvert (2^64) -- big non-scalar / positive MSB

/-! ## Fixed-Width Integers -/

/-- info: -1 -/
#guard_msgs in #eval mkPyISize (-1)
/-- info: 1 -/
#guard_msgs in #eval mkPyUSize 1
/-- info: -1 -/
#guard_msgs in #eval mkPyInt64 (-1)
/-- info: 1 -/
#guard_msgs in #eval mkPyUInt64 1
/-- info: -1 -/
#guard_msgs in #eval mkPyInt32 (-1)
/-- info: 1 -/
#guard_msgs in #eval mkPyUInt32 1
/-- info: -1 -/
#guard_msgs in #eval mkPyInt16 (-1)
/-- info: 1 -/
#guard_msgs in #eval mkPyUInt16 1
/-- info: -1 -/
#guard_msgs in #eval mkPyInt8 (-1)
/-- info: 1 -/
#guard_msgs in #eval mkPyUInt8 1

def testBounds [ToString α] (f : PyInt → Option α) (ns : Array Int) : PyIO (Array String) :=
  ns.mapM fun n => return f (← mkPyInt n) |>.elim "⊥" toString

def testSBounds [ToString α] (f : PyInt → Option α) (minVal maxVal : Int) : PyIO (Array String) :=
  testBounds f #[-1, 1, minVal, maxVal, minVal-1, maxVal+1]

def testUBounds [ToString α] (f : PyInt → Option α) (sz : Nat) : PyIO (Array String) :=
  testBounds f #[-1, 1, sz-1, sz]

/-- info: #["-1", "1", "2147483647", "-2147483648", "⊥", "⊥", "⊥", "⊥"] -/
#guard_msgs in #eval testBounds PyInt.toISize?
  #[-1, 1, Int32.maxValue.toInt, Int32.minValue.toInt,
    UInt64.size, USize.size-1, ISize.minValue.toInt-1, ISize.maxValue.toInt+1]
/-- info: #["⊥", "1", "4294967295", "⊥", "⊥"] -/
#guard_msgs in #eval testBounds PyInt.toUSize?
  #[-1, 1, Int32.size-1, UInt64.size, USize.size]
/-- info: #["-1", "1", "-9223372036854775808", "9223372036854775807", "⊥", "⊥"] -/
#guard_msgs in #eval testSBounds PyInt.toInt64? Int64.minValue.toInt Int64.maxValue.toInt
/-- info: #["⊥", "1", "18446744073709551615", "⊥"] -/
#guard_msgs in #eval testUBounds PyInt.toUInt64? UInt64.size
/-- info: #["-1", "1", "-2147483648", "2147483647", "⊥", "⊥"] -/
#guard_msgs in #eval testSBounds PyInt.toInt32? Int32.minValue.toInt Int32.maxValue.toInt
/-- info: #["⊥", "1", "4294967295", "⊥"] -/
#guard_msgs in #eval testUBounds PyInt.toUInt32? UInt32.size
/-- info: #["-1", "1", "-32768", "32767", "⊥", "⊥"] -/
#guard_msgs in #eval testSBounds PyInt.toInt16? Int16.minValue.toInt Int16.maxValue.toInt
/-- info: #["⊥", "1", "65535", "⊥"] -/
#guard_msgs in #eval testUBounds PyInt.toUInt16? UInt16.size
/-- info: #["-1", "1", "-128", "127", "⊥", "⊥"] -/
#guard_msgs in #eval testSBounds PyInt.toInt8? Int8.minValue.toInt Int8.maxValue.toInt
/-- info: #["⊥", "1", "255", "⊥"] -/
#guard_msgs in #eval testUBounds PyInt.toUInt8? UInt8.size
