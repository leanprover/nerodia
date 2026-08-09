/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean.Environment
import Lean.Compiler.NameMangling
import Lean.Data.Json.FromToJson
import Nerodia.Compiler.Emit.C
import Nerodia.Compiler.Emit.Pyi
import Nerodia.Compiler.Meta.Extension
-- some public Lean.* import is required to ensure Lean is initialized
public import Lean.Data.Name

open System (FilePath)
open Lean (Json ToJson FromJson toJson fromJson?)

namespace Nerodia.Compiler

structure Config where
  leanModule : Lean.Name
  cFile : FilePath
  pyiFile : FilePath
  deriving ToJson, FromJson

structure Output where
  name : String
  deriving ToJson, FromJson

def readConfig (path : FilePath) : IO Config := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= fromJson? with
  | .ok (cfg : Config) => return cfg
  | .error e =>
    throw <| IO.userError s!"invalid configuration: {e}"

def extractPyModule (leanModule : Lean.Name) : IO ModuleDef := do
  Lean.initSearchPath (← Lean.findSysroot)
  -- Extensions are not loaded and initializers not executed.
  -- Neither is required to read the configuration of an imported module,
  -- which is part of its module data, not the loaded extension.
  let env ← Lean.importModules #[leanModule] .empty
    (leakEnv := true) (loadExts := false) (level := .private)
  let some modIdx := env.getModuleIdx? leanModule
    | -- should not be reachable
      throw <| IO.userError "(internal) import without module index"
  let some config := modCfgExt.getStateByIdx? env modIdx |>.join
    | throw <| IO.userError "module lacks a Nerodia configuration"
  -- Only the runtime is initialized by default when possible.
  -- If a Python extension wishes to elaborate Lean code, it can either
  -- dynamically initialize its own meta code using its symbols during the
  -- `importModules` process or use `builtin_initialize` for its Lean
  -- extensions (thereby acting more like a Lean plugin).
  let phases ← id do
    let modIdx : Nat := modIdx
    if h : modIdx < env.header.moduleData.size then
      let isModule := env.header.moduleData[modIdx].isModule
      return if isModule then .runtime else .all
    else
      -- should not be reachable
      throw <| IO.userError s!"(internal) invalid module index: \
        {modIdx} is not less than {env.header.moduleData.size}"
  let leanInit := Lean.mkModuleInitializationFunctionName
    leanModule (env.getModulePackageByIdx? modIdx) phases
  return {config, leanInit, leanModule}

def run
  (cfgFile : FilePath) (outFile? : Option FilePath := none)
: IO Unit := do
  let cfg ← readConfig cfgFile
  let mod ← extractPyModule cfg.leanModule
  writeCFile cfg.cFile mod
  writePyiFile cfg.pyiFile mod
  let out := {name := mod.name : Output}
  let outJson := (toJson out).pretty
  if let some outFile := outFile? then
    IO.FS.writeFile outFile outJson
  else
    IO.print outJson

/-- The main function of the {lit}`nerodiac` executable. -/
public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [cfgFile] =>
      run cfgFile
      return (0 : UInt32)
    | [cfgFile, outFile] =>
      run cfgFile outFile
      return 0
    | _ =>
      IO.eprintln "USAGE: nerodiac <config.json> [<out.json>]"
      return 1
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
