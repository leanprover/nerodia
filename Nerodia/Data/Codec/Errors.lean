/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Codec Error Handling -/

namespace Nerodia

/-- Identifier of a registered Python error handler for codecs. -/
public structure CodecErrors where
  ofString ::
    protected toString : String

namespace CodecErrors

public instance : ToString CodecErrors := ⟨CodecErrors.toString⟩

/-!
## Standard Python Error Handlers

The Lean names of these Python identifiers follow Lean naming conventions
(i.e., lower camel case).
-/

/-- Raise {lit}`UnicodeError` (or a subclass). -/
@[inline] public def strict : CodecErrors := ⟨"strict"⟩

/-- Ignore the malformed data and continue without further notice. -/
@[inline] public def ignore : CodecErrors := ⟨"ignore"⟩

/--
Replace unsupported characters with a replacement marker. On encoding,
use `?` (the ASCII character). On decoding, use `�` (U+FFFD, the official
Unicode replacement character).
-/
@[inline] public def replace : CodecErrors := ⟨"replace"⟩

/--
Replace unsupported characters with backslashed escape sequences.
On encoding,  use hexadecimal form of Unicode code point with formats
{lit}`\xhh`, {lit}`\uxxxx`, {lit}`\Uxxxxxxxx`. On decoding, use hexadecimal
form of byte value with format {lit}`\xhh`.
-/
@[inline] public def backslashReplace : CodecErrors := ⟨"backslashreplace"⟩

/--
On decoding, replace surrogates with their individual surrogate escape
code ranging from {lit}`U+DC80` to {lit}`U+DCFF`. This code will then be turned
back into the surrogate when the {name}`surrogateEscape` error handler is
used when encoding the data.
-/
@[inline] public def surrogateEscape : CodecErrors := ⟨"surrogateescape"⟩

/--
For Unicode codecs, allow encoding and decoding a surrogate code point
({lit}`U+D800` - {lit}`U+DFFF`) as normal code point. Otherwise, these codecs
treat the presence of a lone surrogate as an error.
-/
@[inline] public def surrogatePass : CodecErrors := ⟨"surrogatepass"⟩

/--
When encoding text, replace unsupported characters with XML/HTML numeric
character reference, which is a decimal form of Unicode code point with
format `&#num;`.
-/
@[inline] public def xmlCharRefReplace : CodecErrors := ⟨"xmlcharrefreplace"⟩

/--
When encoding text, replace unsupported characters with {lit}`\N{...}`
escape sequences. What appears in the braces is the {lit}`Name` property
from the Unicode Character Database.
-/
@[inline] public def nameReplace : CodecErrors := ⟨"namereplace"⟩
