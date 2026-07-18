/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Codec
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.ViewMethod

namespace Nerodia

namespace PyBuffer

/--
Decodes a bytes-like object into a string.

This is equivalent to the Python {lit}`str(self, encoding, errors)`.
-/
@[extern "nerodia_py_object_decode", view_method]
public opaque decode (self : @& PyBuffer)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

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
