/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.ViewMethod

namespace Nerodia.PyObject

/--
Returns the type of the object {lean}`self`.

This is equivalent to {lit}`type(self)` in Python.
-/
@[extern "nerodia_py_object_get_type", view_method]
public opaque getType (self : @& PyObject) : CPyBaseIO PyType

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`repr(self)`.
-/
@[extern "nerodia_py_object_repr", view_method]
public opaque repr (self : @& PyObject) : CPyIO PyStr

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`str(self)`.
-/
@[extern "nerodia_py_object_str", view_method]
public opaque str (self : @& PyObject) : CPyIO PyStr

/--
Returns the attribute named {lean}`attr` on {lean}`self`.

This is equivalent to the Python expression {lit}`getattr(self, attr)`.
-/
@[extern "nerodia_py_object_get_attr_by_string", view_method]
public opaque getAttrByString
  (self : @& PyObject) (attr : @& String) : CPyIO PyObject
