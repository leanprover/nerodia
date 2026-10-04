/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Addr
public import Nerodia.Data.Context
public import Nerodia.Data.TypeExpr

namespace Nerodia.Internal.Py

/-- A fixed enumeration of builtin base types. -/
-- A very simple model, it could be made more dynamic in the future.
public inductive Kind
| type
| baseException
| str
| bytes
| int
| tuple
| module
| other
deriving Nonempty, DecidableEq

/-- A fixed inductive of builtin base types. -/
-- A very simple model, it could be made more dynamic in the future.
public inductive DataAux (α : Type u)
| type
| baseException
| str
| bytes
| int
| tuple (xs : Array α)
| module
| other
deriving Nonempty, DecidableEq

@[reducible, expose]
public def DataAux.kind (self : DataAux α) : Kind :=
  match self with
  | .type => .type
  | .baseException => .baseException
  | .str => .str
  | .bytes => .bytes
  | .int => .int
  | .tuple .. => .tuple
  | .module => .module
  | .other => .other

public def DataAux.tupleArray (self : DataAux α) (h : self.kind = .tuple) : Array α :=
  match self with
  | .tuple xs => xs

@[simp, grind =] public theorem DataAux.tupleArray_tuple :
  (tuple xs).tupleArray h = xs := by rfl

/--
The computable portion of the logical Python object model.

Decidably equal by address equality.
-/
public structure InnerModel (α : Type u) where
  addr : Addr
  env : PyEnvironment
  data : DataAux α := .other
  deriving Nonempty

public def InnerModel.kind (self : InnerModel α) : Kind :=
  self.data.kind

@[simp, grind =] public theorem InnerModel.kind_spec :
  kind m = m.data.kind := by rfl

/--
The logical model of a Python object.

Includes static typing information not derivable from the data model
(i.e., {lean}`InnerModel`).
-/
public structure Model extends InnerModel Model where
  hint : TypeExpr
  deriving Nonempty

public abbrev Data := DataAux Model

public def Data.ofKind (k : Kind) : Data :=
  match k with
  | .type => .type
  | .baseException => .baseException
  | .str => .str
  | .bytes => .bytes
  | .int => .int
  | .tuple => .tuple #[]
  | .module => .module
  | .other => .other

@[simp, grind =] public theorem Data.kind_ofKind : (ofKind k).kind = k := by
  cases k <;> rfl

/--
A Python object. A [{lit}`PyObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public structure Raw where
  ofModel ::
    toModel : Model
    deriving Nonempty
