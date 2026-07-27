/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Addr

/-! # Raw C Pointers -/

namespace Nerodia.Internal

/-! ## Nullable Pointers -/

/--
A raw C pointer. May be {lit}`NULL`.

**Not memory safe.** The pointer's lifetime must be manually managed.
It is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`NullableCPtr` objects manually.
-/
public structure NullableCPtr (α : Type u) : Type where
  /--
  Constructs a pointer from a raw address.

  **Safety:** The address must be a pointer to {lean}`α` (if not {lean}`null`).
  -/
  ofNullableAddrUnsafe ::
    nullableAddr : NullableAddr
    nonempty_of_not_isNull_nullableAddr (h : ¬ nullableAddr.IsNull) : Nonempty α
    deriving DecidableEq

namespace NullableCPtr

 /--
  Constructs a pointer from a raw address.

  **Safety:** The address must be a pointer to {lean}`α`.
  -/
@[inline] public def ofAddrUnsafe [Nonempty α] (addr : Addr) : NullableCPtr α :=
  ofNullableAddrUnsafe addr fun _ => inferInstance

public theorem nullableAddr_inj : nullableAddr a = nullableAddr b ↔ a = b := by
  cases a; cases b; simp

@[inline] public protected def null : NullableCPtr α :=
  ⟨null, by simp⟩

public instance : Coe Null (NullableCPtr α) := ⟨fun _ => NullableCPtr.null⟩
public instance : Inhabited (NullableCPtr α) := ⟨null⟩

public abbrev IsNull (self : NullableCPtr α) : Prop :=
  self.nullableAddr.IsNull

@[simp, grind .] public theorem isNull_null : IsNull (α := α) null :=
  NullableAddr.isNull_null

public theorem nonempty_of_not_isNull
  {p : NullableCPtr α} (h : ¬ IsNull p) : Nonempty α
:= p.nonempty_of_not_isNull_nullableAddr <| by simpa [← nullableAddr_inj] using h

end NullableCPtr

/-! ## Non-Null Pointers -/

/--
A raw C pointer.

**Not memory safe.** The pointer's lifetime must be manually managed.
It is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPtr` objects manually.
-/
public structure CPtr (α : Type u) extends NullableCPtr α where
  ofNullableCPtr ::
    not_isNull : ¬ toNullableCPtr.IsNull
    deriving DecidableEq

namespace CPtr

public instance : Coe (CPtr α) (NullableCPtr α) := ⟨toNullableCPtr⟩

/--
Constructs a pointer from a raw address.

**Safety:** The address must be a pointer to {lean}`α`.
-/
@[inline] public def ofAddrUnsafe [Nonempty α] (addr : Addr) : CPtr α :=
  ofNullableCPtr (.ofAddrUnsafe addr) addr.not_isNull

public instance [Nonempty α] : Nonempty (CPtr α) :=
  ⟨ofAddrUnsafe Classical.ofNonempty⟩

@[inline] public def addr (self : CPtr α) : Addr :=
  .ofNullableAddr self.nullableAddr self.not_isNull

public theorem addr_inj : addr a = addr b ↔ a = b := by
  cases a; cases b; simp [← NullableCPtr.nullableAddr_inj, addr]

public theorem nonempty {self : CPtr α} : Nonempty α :=
  self.toNullableCPtr.nonempty_of_not_isNull self.not_isNull

end CPtr
