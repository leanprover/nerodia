/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Data.Types
import all Nerodia.Data.Typing
import all Nerodia.Data.Py.Basic
meta import Nerodia
public import Nerodia
import NerodiaManual.Meta.Precompile

open Nerodia
open Verso.Genre Manual InlineLean

namespace NerodiaManual

variable {x : PyObject} {s : Py str}

#doc (Manual) "Python Typing" =>
%%%
tag := "python-typing"
htmlSplit := .never
%%%

Nerodia has a single baseline representation of Python objects, {lean}`Py`,
which takes as a type parameter a {lean}`Typing`. For example, an instance of
`str` in Python is represented as {lean}`Py str` through its abbrevation,
{lean}`PyStr`. A {lean}`Py` value carries a proof of its typing. For instance,
`s : Py str` implies {lean}`s ⦂ str`.

{docstring Nerodia.Py +hideFields +hideStructureConstructor}
{docstring Nerodia.Typing}
{docstring Nerodia.Typing.HasType}
{docstring Nerodia.Py.attachType}

# Weak Typing

Typing in Python is mutable. Objects can have their type changed by
reassigning their `__class__` attribute, and types themselves can have
their inheritance tree change by reassigning `__bases__`.

As such, most type relations in Python do not hold statically and therefore
cannot be modelled correctly and safely by a pure {lean}`Typing` in Lean.
Nonetheless, statically typing Python objects in Lean is still useful, so
Nerodia provides a mechanism for {deftech}`weak typing`. Objects are annotated
with erased {deftech}`type hints` to indicate the expected type and the
{lean}`Typing` of weak types verifies the presence of its corresponding hint.

For example, it is possible to mutate objects between the many subtypes of
`BaseExcpetion` (e.g., an object can be retyped `Exception`). As such, instances
of these subtypes are weakly typed.

# Strong Typing

While the Python specification leaves the mutability of an object's type
undefined, the CPython implementation places notable restrictions on this
mutability.  Notably, it prevents reassignment between many builtin types
(e.g., `str`).

Nerodia leverages this to provide pure type checks. Their static types (e.g.,
{lean}`PyStr`) then hold a proof of this check through their {lean}`Typing`.
Since many builtin types are also immutable, the data of such types can be
safely accessed in a pure manner (e.g., {lean}`PyStr.toString`).

```lean (name := strCheck)
def testStrInstance (o : PyObject) : IO Unit :=
  if h : o ⦂ str then
    IO.println s!"str: {o.attachType h |>.toString}"
  else
    IO.println "not a str"

#eval PyIO.toIO do testStrInstance (← mkPyInt 1)
#eval PyIO.toIO do testStrInstance (← mkPyStr "hi")
```
```leanOutput strCheck
not a str
```
```leanOutput strCheck
str: hi
```

Still, there are caveats. Foremost, this is not strictly in accordance with the
Python specification, which leaves the mutability of an object's type undefined.
However, CPython's implementation strongly assumes confusion between builtin
types cannot happen (e.g., retyping an `int` to/from a `str` would easily
segfault when used). Weighing these considerations, Nerodia chooses to model
builtin types functionally to make reasoning easier and more pure, accepting
the cost of a potential future breakage in the event of an unlikely, massive
CPython refactor.
