/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Codec Error Handling -/

namespace Nerodia

/-- Identifier of a registered Python encoding. -/
public structure Codec where
  ofString ::
    protected toString : String

namespace Codec

public instance : ToString Codec := ⟨Codec.toString⟩

/-!
## Standard Python Encodings

The Lean names of these Python identifiers follow Lean naming conventions
(i.e., lower camel case).

See the [Python documentation][1] for a for a full list of codecs and
what languages they support.

[1]: https://docs.python.org/3/library/codecs.html#standard-encodings
-/

public abbrev ascii : Codec := ⟨"ascii"⟩
public abbrev latin1 : Codec := ⟨"latin_1"⟩
public abbrev utf8 : Codec := ⟨"utf-8"⟩
public abbrev utf16 : Codec := ⟨"utf-16"⟩
public abbrev utf16LE : Codec := ⟨"utf-16-le"⟩
public abbrev utf16BE : Codec := ⟨"utf-16-be"⟩
public abbrev utf32 : Codec := ⟨"utf-32"⟩
public abbrev utf32LE : Codec := ⟨"utf-32-le"⟩
public abbrev utf32BE : Codec := ⟨"utf-32-be"⟩
