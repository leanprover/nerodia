/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Pointer Addresses -/

namespace Nerodia

/-! ## Nullable Pointer Address -/

/-- A pointer address. May be {lit}`NULL`. -/
public structure NullableAddr where
  private ofUSizeUnsafe ::
    toUSize : USize
    deriving DecidableEq

namespace NullableAddr

/-- The address of a null pointer (i.e., {lit}`NULL` in C). -/
@[inline] public protected def null : NullableAddr :=
  ⟨0⟩ -- `NULL = 0` on Lean-supported platforms

public instance : Inhabited NullableAddr := ⟨NullableAddr.null⟩

public abbrev IsNull (self : NullableAddr) : Prop :=
  self = NullableAddr.null

@[simp] public theorem isNull_null : IsNull NullableAddr.null := by rfl

public abbrev toNat (self : NullableAddr) : Nat :=
  self.toUSize.toNat

end NullableAddr

/-! ## Null -/

/-- The type of the null pointer constant (i.e., {lit}`NULL` in C). -/
-- `Null` is defined as a subtype of `NullableAddr` instead of a singleton
-- inductive in order to retain a `USize` runtime representation, which is
-- necessary for the function signature of `PyMethNoArgs`.
public structure Null where
  addr : NullableAddr
  isNull_addr : addr.IsNull

namespace Null

public theorem addr_inj : addr a = addr b ↔ a = b := by
  cases a; cases b; simp

/-- The null pointer constant (i.e., {lit}`NULL` in C). -/
@[inline] public def null : Null :=
  ⟨NullableAddr.null, rfl⟩

public instance : Inhabited Null := ⟨null⟩
public instance : Coe Null NullableAddr := ⟨fun _ => NullableAddr.null⟩

public instance : Subsingleton Null where
  allEq a b := by simp [← addr_inj, a.isNull_addr, b.isNull_addr]

end Null

export Null (null)

/-! ## Non-Null Pointer Address -/

/-- A pointer address. -/
public structure Addr extends NullableAddr where
  ofNullableAddr ::
    not_isNull : ¬ toNullableAddr.IsNull
    deriving DecidableEq

namespace Addr

public instance : Nonempty Addr :=
  ⟨⟨⟨1⟩, by simp [NullableAddr.null, ← USize.toNat_inj]⟩⟩

public instance : Coe Addr NullableAddr := ⟨toNullableAddr⟩

public theorem toNullableAddr_inj : toNullableAddr a = toNullableAddr b ↔ a = b := by
  cases a; cases b; simp

end Addr
