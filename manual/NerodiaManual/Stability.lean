/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "API Stability" =>
%%%
tag := "stability"
htmlSplit := .never
%%%

While Nerodia is still in development, it nonetheless strives to maintain
stability in its public API across versions. Generally, definitions to be
removed from the public API will undergo a period of deprecation (usually
one version cycle). In the event Nerodia makes changes that break the public API
without deprecation, those changes will be recorded as *breaking changes* in the
{ref "changelog"}[changelog] for that version.

Nerodia uses the module system, and its public API is primarily defined by the
content available through its exported module interface. For instance, `public`
definitions are public API, `private` ones are not. If `import all` is needed to
access a part of Nerodia, that part is not public API and the code relying on it
may break between revisions without warning.

However, there are aspects of Nerodia's exported module interface that are,
nonetheless, not part of its public API. These exceptions are detailed below.

# Module Names
%%%
tag := "module-stability"
%%%

Nerodia is expected to be imported via `import Nerodia`. Submodules of
`Nerodia` (e.g., `Nerodia.Data`) are not part of its public API. Thus, the
definitions within may change, the entire module may removed, or code may
otherwise be reorganized without warning.

# Instances
%%%
tag := "instance-stability"
%%%

Nerodia instances are only partially public API. Nerodia will try to maintain
consistency in what instances are available, but the precise definitions may
change between revisions without warning.

# `@[irreducible, expose]`
%%%
tag := "irreducible-expose"
%%%

Due to the limitations of Lean, both in Nerodia code generation and Lean's own
compiler, some definitions in the public API are marked `@[irreducible, expose]`
instead of having `private` bodies. The bodies of these functions should nonetheless
be considered `private` and may change without warning.

# `Nerodia.Internal`
%%%
tag := "nerodia-internal"
%%%

All definitions within the `Nerodia.Internal` namespace are internal implementation
details and not part of the public API. They can change between revision without
warning. Users should not rely on them.

If you need a definition from the internal namespace, please file a feature
request on the [Nerodia issue tracker][1]. If feasible, we will try to design a
usable public API.

[1]: https://github.com/leanprover/nerodia/issues

# `Nerodia.Compiler`
%%%
tag := "nerodia-compiler"
%%%

Similar to `Nerodia.Internal`, definitions within `Nerodia.Compiler` are also
not part of the public API. The compiler may become part of the public API in
the future, but it currently is not.

{ref "annotations"}[Compiler annotations] like `py_module` and `@[py_module_fn]`
are part of the public API in their user interface and semantics. However, their
meta definitions are part of `Nerodia.Compiler` and, therefore. internal. Their
definitions may change without notice, as long as they maintain the same user
interface.
