/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Addr
public import Nerodia.Data.Context
public import Nerodia.Data.TypeExpr

namespace Nerodia

namespace Internal

/-- A fixed enumeration of builtin base types. -/
-- A very simple model, it could be made more dynamic in the future.
public inductive Py.Kind
| type
| baseException
| str
| bytes
| int
| module
| other
deriving Nonempty, DecidableEq

/-- The logical model of a Python object. -/
public structure Py.Model where
  addr : Addr
  env : PyEnvironment
  hint : TypeExpr
  kind : Py.Kind
  deriving Nonempty

end Internal

/--
A Python object. A [{lit}`PyObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public structure Py.Raw where
  private innerMk ::
    private innerModel : Internal.Py.Model
    deriving Nonempty

namespace Internal.Nerodia.Py.Raw

public noncomputable def ofModel (o : Py.Model) : Py.Raw :=
  .innerMk o

public noncomputable def toModel (o : Py.Raw) : Py.Model :=
  o.innerModel

@[simp, grind =]
public theorem toModel_ofModel : toModel (ofModel m) = m := by
  rfl

end Internal.Nerodia.Py.Raw
