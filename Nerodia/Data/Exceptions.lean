/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.CPyIO

namespace Nerodia

@[extern "nerodia_mk_py_eof_error"]
opaque mkPyEOFError : CPyIO PyEOFError

/-- Raises a {lean}`PyEOFError`. -/
@[inline] public def raisePyEOFError : CPyIO α :=
  Internal.raiseNew <| (mkPyEOFError).promote

@[extern "nerodia_mk_py_type_error"]
opaque mkPyTypeError (msg : @& String) : CPyIO PyTypeError

/-- Raises a {lean}`PyTypeError` with the given message {lean}`msg`. -/
@[inline] public def raisePyTypeError (msg : String) : CPyIO α :=
  Internal.raiseNew <| (mkPyTypeError msg).promote

@[extern "nerodia_mk_py_value_error"]
opaque mkPyValueError (msg : @& String) : CPyIO PyValueError

/-- Raises a {lean}`PyValueError` with the given message {lean}`msg`. -/
@[inline] public def raisePyValueError (msg : String) : CPyIO α :=
  Internal.raiseNew <| (mkPyValueError msg).promote

@[extern "nerodia_mk_py_runtime_error"]
opaque mkPyRuntimeError (msg : @& String) : CPyIO PyRuntimeError

/-- Raises a {lean}`PyRuntimeError` with the given message {lean}`msg`. -/
@[inline] public def raisePyRuntimeError (msg : String) : CPyIO α :=
  Internal.raiseNew <| (mkPyRuntimeError msg).promote

@[extern "nerodia_mk_py_os_error2"]
opaque mkPyOSError2 (errno : UInt32) (strerror : @& String) : CPyIO PyOSError

@[extern "nerodia_mk_py_os_error3"]
opaque mkPyOSError3
  (errno : UInt32) (strerror : @& String) (filename : @& System.FilePath)
: CPyIO PyOSError

@[inline_if_reduce] def mkPyOSError
  (errno : UInt32) (strerror : String) (filename? : Option System.FilePath)
: CPyIO PyOSError :=
  match filename? with
  | some filename => mkPyOSError3 errno strerror filename
  | none => mkPyOSError2 errno strerror

/--
Raises a {lean}`PyOSError` (possibly a subclass) corresponding to the OS-specific
{lean}`errno` with the system error message {lean}`strerror` and optional filename.
-/
@[inline] public def raisePyOSError
  (errno : UInt32) (strerror : String) (filename? : Option System.FilePath := none)
: CPyIO α := Internal.raiseNew <| (mkPyOSError errno strerror filename?).promote

/-- Unpacks a Lean {lean}`IO.Error` and returns the corresponding Python error. -/
@[inline_if_reduce] def mkIOError (e : IO.Error) : CPyIO PyBaseException :=
  match e with
  | .unexpectedEof =>
    mkPyEOFError |>.promote
  | .interrupted fn code details
  | .noFileOrDirectory fn code details =>
    mkPyOSError code details fn |>.promote
  | .inappropriateType fn? code details
  | .invalidArgument fn? code details
  | .noSuchThing fn? code details
  | .permissionDenied fn? code details
  | .resourceExhausted fn? code details
  | .alreadyExists fn? code details =>
    mkPyOSError code details fn? |>.promote
  | .otherError code details
  | .resourceBusy code details
  | .resourceVanished code details
  | .hardwareFault code details
  | .illegalOperation code details
  | .protocolError code details
  | .timeExpired code details
  | .unsatisfiedConstraints code details
  | .unsupportedOperation code details =>
    mkPyOSError code details none |>.promote
  | .userError msg  =>
    mkPyRuntimeError msg |>.promote

open IO.Error in
/--
Unpacks a Lean {lean}`IO.Error` and raises the corresponding Python error.

An {lean}`userError` becomes a {lean}`PyRuntimeError`, a {lean}`unexpectedEof`
becomes a {lean}`PyEOFError`, and everything else becomes a {lean}`PyOSError`
(or one of its subclasses).
-/
@[inline] public def raiseIOError (e : IO.Error) : CPyIO α :=
  Internal.raiseNew (mkIOError e)

@[inline] public def IO.toPyIO (x : IO α) : PyIO α := do
  match (← x.toBaseIO) with
  | .ok a => pure a
  | .error e => raiseIOError e

public instance : MonadLift IO PyIO := ⟨IO.toPyIO⟩
