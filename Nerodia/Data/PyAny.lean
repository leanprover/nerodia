/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Py.Basic

/-! # PyAny -/

namespace Nerodia

/--
A special indicator signifying any acceptable value.
This is analogous to Python's [{lit}`Any`][1].

As a typing, this is propositionally equivalent to {lean}`object`,
but it has different type class instances.

[1]: https://typing.python.org/en/latest/spec/special-types.html#any
-/
public opaque any : Constant

@[irreducible] public def Typing.any : Typing := .object

public instance : CoeDep Constant any Typing := ⟨.any⟩

@[simp, grind =] public theorem Typing.any_eq_object : any = object := by
  unfold any; rfl

public instance : NonemptyPy any :=
  .intro Classical.ofNonempty (by simp)

public instance : DecidablePy any := private_decl%
  (fun _ => isTrue (by simp))

/--
A Python object of unknown type. This is analogous to Python's {lit}`Any`.

As Lean is statically typed, there is little utility in using this type
instead of {name}`PyObject` within Lean code. However, it exists to enable
defining Python functions whose parameters or return should be left untyped.

For example, a module function defined as

```
@[py_module_fn] def foo (o : PyObject) : PyObject := ...
```

will be given the type {lit}`(o: object) -> object` by Nerodia, whereas

```
@[py_module_fn] def foo (o : PyAny) : PyAny := ...
```

will have the type {lit}`(o)` with no annotated parameter or return types.
-/
public abbrev PyAny := PyObjectView <| Py any

public instance : ViewPy any PyAny := ⟨rfl⟩
