/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
public import Nerodia
meta import Lean

/-! # Public API

Verifies the list of {lit}`public` definitions exposed by {module}`Nerodia`
within the {lit}`Nerodia` namespace (excluding {lit}`Nerodia.Internal`).
-/

open Lean
open System (FilePath)

inductive Mode | check | update

meta def publicApi (mode : Mode) : MetaM Unit := do
  let env ← getEnv
  -- Since this module publicly imports `Nerodia`, its exporting environment
  -- sees exactly the `public` definitions importers of `Nerodia` would.
  let expEnv := env.setExporting true
  -- Instances and their generated definitions (e.g., `decEq`) are grouped
  -- separately from other definitions
  let isInstRelated (n : Name) : Bool := Id.run do
    let mut n := n
    while n != .anonymous do
      if Meta.isInstanceCore env n then return true
      n := n.getPrefix
    return false
  let mut defs := #[]
  let mut insts := #[]
  for (name, info) in env.constants.toList do
    unless (`Nerodia).isPrefixOf name do continue
    if (`Nerodia.Internal).isPrefixOf name then continue
    if (`Nerodia.Compiler).isPrefixOf name then continue
    -- Skip auto-generated auxiliaries (e.g., `casesOn`, `noConfusion`)
    if info matches .recInfo _ then continue
    if name.isInternalDetail || isAuxRecursor env name || isNoConfusion env name then
      continue
    if let .str _ s := name then
      if #["noConfusionType", "ctorIdx", "inj", "injEq",
          "sizeOf_spec", "congr_simp"].contains s then
        continue
    unless expEnv.contains name do continue
    if isInstRelated name then
      insts := insts.push name
    else
      defs := defs.push name
  let rec isType
    | .sort _ => true
    | .forallE (body := b) .. => isType b
    | _ => false
  let newConstants := defs.qsort (·.toString < ·.toString) |>.map fun name =>
    if Linter.isDeprecated env name then
      s!"{name} (deprecated)"
    else if env.hasExposedBody name then
      if getReducibilityStatusCore env name matches .irreducible then
        s!"{name} (irreducible)"
      else if env.isProjectionFn name then
        s!"{name} (proj)"
      else if env.find? name |>.any fun | .defnInfo v => isType v.type | _ => false then
        s!"{name} (type abbrev)"
      else
        s!"{name} (exposed)"
    else
      name.toString
  let newInstances := insts.map (·.toString) |>.qsort (· < ·)
  let constantsFile : FilePath := "tests/NerodiaTests/publicApi/constants.txt"
  let instancesFile : FilePath := "tests/NerodiaTests/publicApi/instances.txt"
  match mode with
  | .check =>
    let checkDiff pre new path : IO Bool := do
      let old := (← IO.FS.readFile path).lines.toStringArray
      let diff := Diff.diff old new
      if diff.any (·.1 != .skip) then
        IO.print pre
        if old.size != new.size then
          IO.println s!"{old.size} -> {new.size}"
        else
          IO.println old.size
        IO.print (Diff.linesToString diff)
        return true
      return false
    let c1 ← checkDiff "# Constants: " newConstants constantsFile
    let c2 ← checkDiff "# Instances: " newInstances instancesFile
    if c1 || c2 then
      throwError "public API changed"
    else if Elab.inServer.get (← getOptions) then
      IO.println s!"Constants: {newConstants.size}"
      IO.println s!"Instances: {newInstances.size}"
  | .update =>
    let writeFile path defs := do
      let h ← IO.FS.Handle.mk path .write
      for d in defs do
        h.putStrLn d
    writeFile constantsFile newConstants
    writeFile instancesFile newInstances

#eval publicApi .check
