/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia
meta import Lean

/-!
# Python Signature Inference

This test verifies the Python signatures the Nerodia compiler generates.
It serves as a faster supplement to a full {lit}`lean2py` integration test.
-/

open Nerodia

/-! ## Setup -/

py_module "test"

open Lean Elab Command in
elab "#check_fn " sig:declSig : command => withoutModifyingEnv do
  elabCommand <| ← `(
    set_option linter.unusedVariables.funArgs false in
    @[py_module_fn] opaque $(mkIdent `test) $sig)
  let some df := Compiler.modCfgExt.getState (← getEnv) |>.get!.methods.back?
    | return
  logInfo df.pySig

open Lean Elab Command in
elab "#check_attr " ty:term : command => withoutModifyingEnv do
  elabCommand <| ← `(
    set_option linter.unusedVariables.funArgs false in
    @[py_module_attr] opaque $(mkIdent `test) : $ty)
  let some df := Compiler.modCfgExt.getState (← getEnv) |>.get!.attrs.back?
    | return
  logInfo (df.ty?.getD "")

open Lean Elab Command in
elab "#check_name " name:(ident <|> str) : command => withoutModifyingEnv do
  if name.raw.isIdent then
    let name : Ident := ⟨name.raw⟩
    elabCommand <| ← `(
      set_option linter.unusedVariables.funArgs false in
      @[py_module_fn] opaque $name : Unit)
  else
    let name : StrLit := ⟨name.raw⟩
    elabCommand <| ← `(
      set_option linter.unusedVariables.funArgs false in
      @[py_module_fn $name] opaque $(mkIdent `test) : Unit)
  let some df := Compiler.modCfgExt.getState (← getEnv) |>.get!.methods.back?
    | return
  logInfo df.name

/-! ## Tests -/

/-! ### Naming -/

/-- info: (_: str, /) -> None -/
#guard_msgs in #check_fn (_x : String) : Unit

/-- info: (_1: str, _2: str, /) -> None -/
#guard_msgs in #check_fn (_ _ : String) : Unit

/-- error: Invalid argument name 'α': non-ASCII names are not supported -/
#guard_msgs in #check_fn (α : String) : Unit

/-- error: Invalid argument name '0': not a valid Python name -/
#guard_msgs in #check_fn («0» : String) : Unit

/-- error: Invalid argument name 'lambda': reserved Python keyword -/
#guard_msgs in #check_fn (lambda : String) : Unit

open Lean Elab Command in
/-- info: (_: str, /) -> None -/
#guard_msgs in run_cmd elabCommand <|
  ← `(#check_fn (x : String) : Unit)

open Lean Elab Command in
/-- info: (_: str, /) -> None -/
#guard_msgs in run_cmd elabCommand <|
  ← `(#check_fn ($(mkIdent (.num .anonymous 0)) : String) : Unit)

open Lean Elab Command in
/-- error: invalid binder name `x.0`, it must be atomic -/
#guard_msgs in run_cmd elabCommand <|
  ← `(#check_fn ($(mkIdent (`x |>.num 0)) : String) : Unit)

/-- info: input -/
#guard_msgs in #check_name input -- keyword (`in`) as prefix

/-- info: input -/
#guard_msgs in #check_name "input"

/-- info: __int__ -/
#guard_msgs in #check_name __int__

/-- info: __int__ -/
#guard_msgs in #check_name "__int__"

/-- error: Invalid declaration name 'lambda': reserved Python keyword -/
#guard_msgs in #check_name lambda

/-- error: Invalid declaration name 'lambda': reserved Python keyword -/
#guard_msgs in #check_name "lambda"

open Lean Elab Command in
/-- error: Invalid declaration name 'x.0': Lean name does not end with a string -/
#guard_msgs in run_cmd elabCommand <|
  ← `(#check_name $(mkIdent (`x |>.num 0)))

/-! ### Monads -/

/-- info: () -> None -/
#guard_msgs in #check_fn : Unit

/-- info: None -/
#guard_msgs in #check_attr BaseIO Unit

/-- info: () -> None -/
#guard_msgs in #check_fn : BaseIO Unit

/-- info: None -/
#guard_msgs in #check_attr PyBaseIO Unit

/-- info: () -> None -/
#guard_msgs in #check_fn : PyBaseIO Unit

/-- info: Never -/
#guard_msgs in #check_attr PyIO Empty

/-- info: () -> Never -/
#guard_msgs in #check_fn : PyIO Empty

/-! ### {lean}`Py`-only Types -/

/-- info: -/
#guard_msgs in #check_attr PyIO PyAny

/-- info: (o, /) -/
#guard_msgs in #check_fn (o : PyAny) : PyIO PyAny

/-- info: object -/
#guard_msgs in #check_attr PyIO PyObject

/-- info: (o: object, /) -> object -/
#guard_msgs in #check_fn (o : PyObject) : PyIO PyObject

/-- info: Buffer -/
#guard_msgs in #check_attr PyIO PyBuffer

/-- info: (buf: Buffer, /) -> Buffer -/
#guard_msgs in #check_fn (buf : PyBuffer) : PyIO PyBuffer

/-- info: type -/
#guard_msgs in #check_attr PyIO PyType

/-- info: (bs: type, /) -> type -/
#guard_msgs in #check_fn (bs : PyType) : PyIO PyType

/-- info: bytes -/
#guard_msgs in #check_attr PyIO PyBytes

/-- info: (bs: bytes, /) -> bytes -/
#guard_msgs in #check_fn (bs : PyBytes) : PyIO PyBytes

/-- info: ModuleType -/
#guard_msgs in #check_attr PyIO PyModule

/-- info: (bs: ModuleType, /) -> ModuleType -/
#guard_msgs in #check_fn (bs : PyModule) : PyIO PyModule

/-! ### Lean Types -/

/-- info: str -/
#guard_msgs in #check_attr String

/-- info: (s: str, /) -> str -/
#guard_msgs in #check_fn (s : String) : String

-- TODO: Support `ByteArray` as a result type.
/-- info: (b: Buffer, /) -> None -/
#guard_msgs in #check_fn (b : ByteArray) : Unit

/-- info: int -/
#guard_msgs in #check_attr Int

/-- info: (n: int, /) -> int -/
#guard_msgs in #check_fn (n : Int) : Int

/-- info: int -/
#guard_msgs in #check_attr Nat

/-- info: (n: int, /) -> int -/
#guard_msgs in #check_fn (n : Nat) : Nat

/-- info: int -/
#guard_msgs in #check_attr Fin 2

/-- info: (n: int, /) -> int -/
#guard_msgs in #check_fn (n : Fin 0) : Fin 1
