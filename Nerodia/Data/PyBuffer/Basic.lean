/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Codec
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.Internal.ViewMethod

namespace Nerodia

/--
Returns whether {lean}`self` currently supports the buffer interface.

**Safety:** Users must ensure a Python context exists.
-/
@[extern "nerodia_py_object_check_buffer"]
opaque PyObject.checkBufferUnsafe (self : @& PyObject) : BaseIO Bool

/--
Returns {lean}`self` as a {lean}`PyBuffer` if it currently supports the buffer
interface.

**Warning:** It is possible for an object's type to be mutated after this
call such that it is no longer a buffer. Thus, this function comes with no
strong typing guarantees.
-/
@[inline, view_method]
public def PyObject.getPyBuffer? (self : PyObject) : PyBaseIO (Option PyBuffer) := do
  let ok ← self.checkBufferUnsafe
  Runtime.hold (← Internal.getPyThreadCtxUnsafe)
  return if ok then some (Internal.mkPyBuffer self) else none

namespace PyBuffer

/--
Returns the bytes of the buffer as a Lean {lean}`ByteArray`.

**Safety:** Users must ensure a Python context exists.
-/
@[extern "nerodia_py_buffer_get_byte_array"]
opaque getByteArrayUnsafe (self : @& PyBuffer) : BaseIO (Option ByteArray)

open Internal Nerodia in
/-- Returns the bytes of the buffer as a Lean {lean}`ByteArray`. -/
@[view_method]
public opaque getByteArray (self : @& PyBuffer) : PyIO ByteArray := .ofPyBaseIOUnsafe do
  let a? ← self.getByteArrayUnsafe
  Runtime.hold (← Internal.getPyThreadCtxUnsafe)
  return a?

/--
Decodes a bytes-like object into a string.

This is equivalent to the Python {lit}`str(self, encoding, errors)`.
-/
@[extern "nerodia_py_buffer_decode", view_method]
public opaque decode (self : @& PyBuffer)
  (encoding : @& CodecEncoding) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Decodes bytes as a UTF-8-encoded string.

This is equivalent to {lean}`self.decode .utf8 .strict`.
-/
@[inline, view_method]
public def decodeUTF8 (self : @& PyBuffer) : CPyIO PyStr :=
  self.decode .utf8 .strict

@[simp, grind =]
public theorem decodeUTF8_eq_decode :
  decodeUTF8 b = decode b .utf8 .strict
:= by rfl
