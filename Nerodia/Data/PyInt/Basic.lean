/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO

/-!
# Python Integer Basics

This module contains definitions for converting Python integers to/from
Lean types and computing basic properties about them.
-/

namespace Nerodia

open Classical in
/-- Returns whether {lean}`self` is an instance of {lit}`int`. -/
@[extern "nerodia_py_object_is_int_instance"]
def PyObject.isIntInstance (self : @& PyObject) : Bool :=
  self ⦂ int

open PyObject in
public instance : DecidablePy int := private_decl%
  (Internal.decPy isIntInstance (by simp [isIntInstance]))

/-! ## Lean to {name}`PyInt` Conversion -/

/--
Creates a Python integer from a
two's complement encoding in little-endian byte order.
-/
@[extern "nerodia_mk_py_int_le"]
opaque mkPyIntLE (n : @& ByteArray) : CPyIO PyInt

@[export nerodia_mk_big_py_int]
partial def mkBigPyInt (n : Int) : CPyIO PyInt :=
  mkPyIntLE (toByteArrayLE n)
where
  @[inline] toByteArrayLE (n : Int) : ByteArray :=
    loop (ByteArray.emptyWithCapacity 32) n
  loop bs n :=
    let n' := n / 256
    let bs := bs.push n.toInt8.toUInt8
    if n = n' then bs else loop bs n'

/-- Creates a Python integer from a Lean integer. -/
@[extern "nerodia_mk_py_int"]
public opaque mkPyInt (n : @& Int) : CPyIO PyInt

/-- Creates a Python integer from a nonnegative Lean integer. -/
@[extern "nerodia_mk_py_nat"]
public def mkPyNat (n : @& Nat) : CPyIO PyInt := mkPyInt n

/-- Creates a Python integer from a bounded, nonnegative Lean integer. -/
@[inline] public def mkPyFin (m : Fin n) : CPyIO PyInt := mkPyNat m

/-! ### Fixed-Width Integers -/

/-- Creates a Python integer from a native signed word. -/
@[extern "nerodia_mk_py_isize"]
public def mkPyISize (n : ISize) : CPyIO PyInt := mkPyInt n.toInt

/-- Creates a Python integer from a native unsigned word. -/
@[extern "nerodia_mk_py_usize"]
public def mkPyUSize (n : USize) : CPyIO PyInt := mkPyNat n.toNat

/-- Creates a Python integer from a native 64-bit signed integer. -/
@[extern "nerodia_mk_py_int64"]
public def mkPyInt64 (n : Int64) : CPyIO PyInt := mkPyInt n.toInt

/-- Creates a Python integer from a native 64-bit unsigned integer. -/
@[extern "nerodia_mk_py_uint64"]
public def mkPyUInt64 (n : UInt64) : CPyIO PyInt := mkPyNat n.toNat

/-- Creates a Python integer from a native 32-bit signed integer. -/
@[extern "nerodia_mk_py_int32"]
public def mkPyInt32 (n : Int32) : CPyIO PyInt := mkPyInt n.toInt

/-- Creates a Python integer from a native 32-bit unsigned integer. -/
@[extern "nerodia_mk_py_uint32"]
public def mkPyUInt32 (n : UInt32) : CPyIO PyInt := mkPyNat n.toNat

/-- Creates a Python integer from a native 16-bit signed integer. -/
@[inline] public def mkPyInt16 (n : Int16) : CPyIO PyInt := mkPyInt32 n.toInt32

/-- Creates a Python integer from a native 16-bit unsigned integer. -/
@[inline] public def mkPyUInt16 (n : UInt16) : CPyIO PyInt := mkPyUInt32 n.toUInt32

/-- Creates a Python integer from a native 8-bit signed integer (i.e., a byte). -/
@[inline] public def mkPyInt8 (n : Int8) : CPyIO PyInt := mkPyInt32 n.toInt32

/-- Creates a Python integer from a native 8-bit unsigned integer (i.e., a byte). -/
@[inline] public def mkPyUInt8 (n : UInt8) : CPyIO PyInt := mkPyUInt32 n.toUInt32

/-! ## {name}`PyInt` to Lean Conversion -/

namespace PyInt

@[extern "nerodia_py_int_to_byte_array_le"]
opaque toByteArrayLE' (self : @& PyInt) : {bs : ByteArray // 0 < bs.size } :=
  ⟨.mk #[default], by simp [ByteArray.size]⟩

/--
Returns the two's-complement encoding of
{lean}`self` in little-endian byte order.
-/
@[inline] public def toByteArrayLE (self : @& PyInt) : ByteArray :=
  self.toByteArrayLE'.val

public theorem size_toByteArrayLE_pos : 0 < (toByteArrayLE self).size :=
  self.toByteArrayLE'.property

@[extern "nerodia_py_int_to_byte_array_be"]
opaque toByteArrayBE' (self : @& PyInt) : {bs : ByteArray // 0 < bs.size } :=
  ⟨.mk #[default], by simp [ByteArray.size]⟩

/--
Returns the two's-complement encoding of
{lean}`self` in big-endian byte order.
-/
@[inline] public def toByteArrayBE (self : @& PyInt) : ByteArray :=
  self.toByteArrayBE'.val

public theorem size_toByteArrayBE_pos : 0 < (toByteArrayBE self).size :=
  self.toByteArrayBE'.property

/-- Returns the integer value of {lean}`self` as a Lean {lean}`Int`.-/
@[inline] public def toInt (self : @& PyInt) : Int :=
  ofByteArrayBE self.toByteArrayBE size_toByteArrayBE_pos
where ofByteArrayBE (bs : ByteArray) (h : 0 < bs.size) := Id.run do
  let mut n := (bs[0]'h).toInt8.toInt
  for h : i in 1...bs.size do
    n := n * 256 + bs[i].toNat
  return n

@[inline] public protected def toString (self : PyInt) : String :=
  toString self.toInt

public instance : ToString PyInt := ⟨PyInt.toString⟩

@[extern "lean_int_to_nat"] -- in `lean.h` but no def in core
def intToNat (n : Int) (h : 0 ≤ n) : Nat :=
  n.natAbs

/--
Returns the integer value of {lean}`self` as a Lean {lean}`Nat`.
If {lean}`self` is negative, returns {lean}`none`.
-/
@[inline] public def toNat? (self : @& PyInt) : Option Nat := do
  let n := self.toInt
  if h : n < 0 then
    none
  else
    return intToNat n (Int.le_of_not_gt h)

@[inline] def toIntLECore?
  (self : PyInt) (minVal maxVal : Int)
  (f : (n : Int) → minVal ≤ n → n ≤ maxVal → α)
: Option α := do
  let n := self.toInt
  if h : minVal ≤ n ∧ n ≤ maxVal then
    return f n h.1 h.2
  else
    none

@[inline] def toNatLTCore?
  (self : PyInt) (n : Nat) (f : (m : Nat) → m < n → α)
: Option α := do
  let m ← self.toNat?
  if h : m < n then
    return f m h
  else
    none

/--
Returns the integer value of {lean}`self` as a Lean {lean}`Fin`.
If {lean}`self` is negative or at least {lean}`n`, returns {lean}`none`.
-/
@[inline] public def toFin? (self : @& PyInt) : Option (Fin n) :=
  self.toNatLTCore? n .mk

/-! ### Fixed-Width Integers -/

/--
Returns the integer value of {lean}`self` as a native signed word.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toISize? (self : @& PyInt) : Option ISize :=
  self.toIntLECore? ISize.minValue.toInt ISize.maxValue.toInt .ofIntLE

/--
Returns the integer value of {lean}`self` as a native unsigned word.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toUSize? (self : PyInt) : Option USize :=
  self.toNatLTCore? USize.size .ofNatLT

/--
Returns the integer value of {lean}`self` as a native 64-bit signed integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toInt64? (self : @& PyInt) : Option Int64 :=
  self.toIntLECore? Int64.minValue.toInt Int64.maxValue.toInt .ofIntLE

/--
Returns the integer value of {lean}`self` as a native 64-bit unsigned integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toUInt64? (self : PyInt) : Option UInt64 :=
  self.toNatLTCore? UInt64.size .ofNatLT

/--
Returns the integer value of {lean}`self` as a native 32-bit signed integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toInt32? (self : @& PyInt) : Option Int32 :=
  self.toIntLECore? Int32.minValue.toInt Int32.maxValue.toInt .ofIntLE

/--
Returns the integer value of {lean}`self` as a native 32-bit unsigned integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toUInt32? (self : @& PyInt) : Option UInt32 :=
  self.toNatLTCore? UInt32.size .ofNatLT


/--
Returns the integer value of {lean}`self` as a native 16-bit signed integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toInt16? (self : @& PyInt) : Option Int16 :=
  self.toIntLECore? Int16.minValue.toInt Int16.maxValue.toInt .ofIntLE

/--
Returns the integer value of {lean}`self` as a native 16-bit unsigned integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toUInt16? (self : @& PyInt) : Option UInt16 :=
  self.toNatLTCore? UInt16.size .ofNatLT

/--
Returns the integer value of {lean}`self` as a native 8-bit signed integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toInt8? (self : @& PyInt) : Option Int8 :=
  self.toIntLECore? Int8.minValue.toInt Int8.maxValue.toInt .ofIntLE

/--
Returns the integer value of {lean}`self` as a native 8-bit unsigned integer.
If {lean}`self` is out of range, returns {lean}`none`.
-/
@[inline] public def toUInt8? (self : @& PyInt) : Option UInt8 :=
  self.toNatLTCore? UInt8.size .ofNatLT
