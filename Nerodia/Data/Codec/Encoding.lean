/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Codec Encoding -/

namespace Nerodia

/-- Identifier of a registered Python encoding. -/
public structure CodecEncoding where
  ofString ::
    protected toString : String

namespace CodecEncoding

public instance : ToString CodecEncoding := ⟨CodecEncoding.toString⟩

/-!
## Standard Python Encodings

The Lean names of these Python identifiers follow Lean naming conventions
(i.e., lower camel case).

See the [Python documentation][1] for a full list of encodings and what
languages they support.

[1]: https://docs.python.org/3/library/codecs.html#standard-encodings
-/

@[inline] public def ascii : CodecEncoding := ⟨"ascii"⟩
@[inline] public def latin1 : CodecEncoding := ⟨"latin_1"⟩
@[inline] public def utf8 : CodecEncoding := ⟨"utf-8"⟩
@[inline] public def utf16 : CodecEncoding := ⟨"utf-16"⟩
@[inline] public def utf16LE : CodecEncoding := ⟨"utf-16-le"⟩
@[inline] public def utf16BE : CodecEncoding := ⟨"utf-16-be"⟩
@[inline] public def utf32 : CodecEncoding := ⟨"utf-32"⟩
@[inline] public def utf32LE : CodecEncoding := ⟨"utf-32-le"⟩
@[inline] public def utf32BE : CodecEncoding := ⟨"utf-32-be"⟩
