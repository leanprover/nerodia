/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Codec
public import Nerodia.Data.Types
public import Nerodia.Data.OfPyArg
public import Nerodia.Data.MkPyResult
public import Nerodia.Data.Py.Ops
public import Nerodia.Data.PyType.Basic
public import Nerodia.Data.Exceptions
public import Nerodia.Control.CPyIO
meta import Nerodia.ViewMethod

namespace Nerodia

/-- Creates a Python string from a Lean string. -/
@[extern "nerodia_mk_py_str"]
public opaque mkPyStr (s : @& String) : CPyIO PyStr

public instance : MkCPyResult String str := ⟨mkPyStr⟩

/-- Decodes a Lean {name}`ByteArray` into a Python string. -/
@[extern "nerodia_decode"]
public opaque decode (bytes : @& ByteArray)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Returns the UTF8-encoded value of {lean}`self` as a Lean {lean}`String`.

If the string contains lone surrogates (and is thus not valid UTF-8),
they will be replaced with `�` (U+FFFD, the official Unicode replacement
character), following Lean's standard lossy encoding.
-/
-- This function is pure because the string data of instances of `str` is immutable.
@[extern "nerodia_py_str_to_string"]
public opaque PyStr.toString (self : @& PyStr) : String

public instance : ToString PyStr := ⟨PyStr.toString⟩

@[inline] public def raiseArgTypeMismatch
  (fn : String) (i : Nat ) (arg : PyObject) (expected : TypeExpr)
: PyIO α := do
  let actual ← (← arg.getType).getQualName
  raisePyTypeError s!"{fn} argument {i} must be {expected}, got {actual}"

public instance : OfPyArg String str where
  ofPyArg fn i arg :=
    if h : arg.isStrInstance then
      return (PyStr.mk arg h).toString
    else raiseArgTypeMismatch fn i arg str

/--
Returns the string encoded as bytes.

This is equivalent to the Python {lit}`str.encode(self, encoding, errors)`.
-/
@[extern "nerodia_py_str_encode"]
public opaque PyStr.encode (self : @& PyStr)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyBytes

/--
Returns the UTF-8-encoded value of the string as bytes.

This is equivalent to {lean}`self.encode .utf8 .strict` but more efficient.
-/
@[extern "nerodia_py_str_encode_utf8"]
public abbrev PyStr.encodeUTF8 (self : @& PyStr) : CPyIO PyBytes :=
  self.encode .utf8 .strict
