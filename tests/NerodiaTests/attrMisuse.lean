/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Nerodia

/-! # Attribute Misuse

Tests the errors raised on invalid uses of Nerodia attributes.
-/

open Nerodia

/-! ## Attribute use before {kw}`py_module` -/

/--
error: Cannot add attribute `[py_module_init]`:
A Python module must first be configured with `py_module`.
-/
#guard_msgs in
@[py_module_init] opaque initNoModule : PyModuleInit

/--
error: Cannot add attribute `[py_module_attr]`:
A Python module must first be configured with `py_module`.
-/
#guard_msgs in
@[py_module_attr] opaque attrNoModule : Unit

/--
error: Cannot add attribute `[py_module_fn]`:
A Python module must first be configured with `py_module`.
-/
#guard_msgs in
@[py_module_fn] opaque fnNoModule : Unit

/-! ## {kw}`py_module` misuse -/

/-- error: Invalid module name 'α': non-ASCII names are not supported -/
#guard_msgs in py_module "a.α"

/-- error: Invalid module name '0': not a valid Python name -/
#guard_msgs in py_module "foo.0.bar"

/-- error: Invalid module name 'lambda': reserved Python keyword -/
#guard_msgs in py_module "lambda.λ"

py_module "test.ok"

/-! ## {attr}`@[py_module_init]` -/

/--
error: Cannot add attribute `[py_module_init]`: Declaration `initBadType` has type
  Unit
but `[py_module_init]` can only be added to declarations of type
  PyModuleInit
-/
#guard_msgs in
@[py_module_init] opaque initBadType : Unit

/-! ## {attr}`@[py_module_fn]` -/

/-- error: All parameters of a `@[py_module_fn]` definition must be explicit. -/
#guard_msgs in
@[py_module_fn] opaque fnNonExplicit {α : Type u} : Unit
