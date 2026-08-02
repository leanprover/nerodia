/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO

namespace Nerodia

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

/-- Creates a Python integer from a nonnegative Lean integer (i.e., a {lean}`Nat`). -/
@[extern "nerodia_mk_py_nat"]
public opaque mkPyNat (n : @& Nat) : CPyIO PyInt

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

/-- Returns the numeric value of {lean}`self` as a Lean {lean}`Int`.-/
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
