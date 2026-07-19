/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Nerodia.Data.CPtr
public import Nerodia.Data.Types
public import Nerodia.Data.OfPyArg
public import Nerodia.Data.Exceptions
public import Nerodia.Control.CPyIO

/-!
# Pythom Export Types

This module defines the types of functions exported from Lean to C for Python.
-/

namespace Nerodia

/-! ## CPyArg -/

/--
A raw Python function argument (a borrowed Python object reference).

**Not memory safe.** The reference must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyArg` objects manually.
-/
public structure CPyArg (T : TypePred := .object) where
  private ofCPtrUnsafe ::
    private toCPtrUnsafe : Internal.CPtr (Py T)

/--
Wraps a borrowed Python object reference into a memory-managed Lean object.

**Memory Safety:** Users must ensure the reference currently valid
(e.g., it has not escaped its original function).
-/
@[extern "nerodia_py_context_mk_arg"]
def Internal.PyContext.mkArgUnsafe
  (ctx : @& PyContext) (arg : CPyArg T)
: (Py T) := Classical.choice arg.toCPtrUnsafe.nonempty

/--
A raw C pointer array of Python function arguments
(borrowed Python object references).

**Not memory safe.** The references must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyArgs` objects manually.
 -/
public structure CPyArgs where
  private ofAddrUnsafe ::
    private addr : Addr

@[extern "nerodia_py_context_mk_args"]
opaque Internal.PyContext.mkArgsUnsafe
  (ctx : @& PyContext) (args : CPyArgs) (nargs : USize) : Array PyObject

@[extern "nerodia_py_context_mk_nth_arg"]
opaque Internal.PyContext.mkNthArgUnsafe
  (ctx : @& PyContext) (args : CPyArgs) (i : USize) : PyObject

/-- Internal function for {lit}`@[py_module_fn]`.  -/
@[inline] public def Internal.ofPyArgUnsafe
  [OfPyArg α T] (fn : String) (i : USize) (args : CPyArgs)
: PyIO α := do
  let obj := ((← getPyContextUnsafe).mkNthArgUnsafe args i)
  OfPyArg.ofPyArg fn (i.toNat+1) obj

/-! ## Python Method Types -/

open Internal (getPyContextUnsafe)

/-! ### PyMethNoArgs -/

/-- The type of a Python method with no arguments. -/
@[expose] -- for codegen
public def PyMethNoArgs :=
  (self : CPyArg) → Null → CPyIO Py.Raw

@[inline] public def PyMethNoArgs.ofPyIO
  (x : (self : PyObject) → PyIO PyAny)
: PyMethNoArgs := fun self _ => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  x self

@[inline] public def PyMethNoArgs.ofPyIO'
  (x : PyIO PyAny)
: PyMethNoArgs := ofPyIO fun _ => x

@[inline] public def PyMethNoArgs.ofCPyIO
  [IsPy α] (x : CPyIO α)
: PyMethNoArgs := fun _ _ => x.raw

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethNoArgs
  (x : CPyIO Py.Raw)
: PyMethNoArgs := PyMethNoArgs.ofCPyIO x

/-! ### PyMethFastCall -/

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethFastCall :=
  (self : CPyArg) → (args : CPyArgs) → (nargs : USize) → CPyIO Py.Raw

@[inline] public def PyMethFastCall.ofPyIO
  (x : (self : PyObject) → (args : Array PyObject) → PyIO (Py T))
: PyMethFastCall := fun self args nargs => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let args := ctx.mkArgsUnsafe args nargs
  x self args

/-- Raises a {lean}`PyTypeError` indicating {lit}`fn` was called with the wrong number of arguments. -/
@[inline] def raiseArityNotEq (fn : String) (expected given : USize) : CPyIO α :=
  raisePyTypeError s!"{fn} takes exactly {expected} arguments ({given} given)"

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethFastCallUnsafe
  (fn : String) (arity : USize)
  (x : (args : CPyArgs) → PyResultIO Py.Raw)
: PyMethFastCall := fun _ args nargs =>
  if nargs = arity then
    x args |>.toCPyIO.raw
  else
    raiseArityNotEq fn arity nargs

/-! ### PyMethO -/

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethO :=
  (self : CPyArg) → (arg : CPyArg) → CPyIO Py.Raw

@[inline] public def PyMethO.ofPyIO
  (x : (self : PyObject) → (arg : PyObject) → PyIO (Py T))
: PyMethO := fun self arg => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let arg := ctx.mkArgUnsafe arg
  x self arg

@[inline] public def PyMethO.ofPyIO'
  (x : (arg : PyObject) → PyIO (Py T))
: PyMethO := ofPyIO fun _ => x

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethO
  (x : (arg : PyObject) → PyResultIO Py.Raw)
: PyMethO := fun _ arg =>
  PyResultIO.toCPyIO <| PyBaseIO.bindPyResultIO getPyContextUnsafe fun ctx =>
    x (ctx.mkArgUnsafe arg)

/-! ## PyModuleInit -/

/-- The type of a Python module initialization function. -/
@[expose] -- for codegen
public def PyModuleInit :=
  (mod : CPyArg .module) → CPyUnitIO

@[inline] public def PyModuleInit.ofPyIO
  (x : PyModule → PyIO Unit)
: PyModuleInit := fun mod => PyIO.toCPyUnitIO do
  let ctx ← getPyContextUnsafe
  x (ctx.mkArgUnsafe mod)

public instance : Inhabited PyModuleInit := ⟨.ofPyIO fun _ _ => return⟩

/-! ## PyAttrInit -/

@[expose] -- for codegen
public def PyAttrInit :=
  CPyIO Py.Raw

@[inline] public def PyAttrInit.ofCPyIO (x : CPyIO α) : PyAttrInit :=
  x.raw

/-- Internal function for {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkPyAttrInit (x : CPyIO Py.Raw) : PyAttrInit :=
  PyAttrInit.ofCPyIO x
