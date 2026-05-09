/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean.Environment
import Lean.Compiler.NameMangling
import Nerodia.Compiler.Emit.C
import Nerodia.Compiler.Emit.Pyi
import Nerodia.Compiler.ModuleConfig.Extension
public import Lean.Data.Json.FromToJson

open System (FilePath)
open Lean (Json ToJson FromJson toJson fromJson?)

namespace Nerodia

public structure CompilerConfig where
  leanModule : Lean.Name
  cFile : FilePath
  pyiFile : FilePath
  deriving ToJson, FromJson

public structure CompilerOutput where
  name : String
  deriving ToJson, FromJson

namespace Compiler

public def readConfig (path : FilePath) : IO CompilerConfig := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= fromJson? with
  | .ok (cfg : CompilerConfig) => return cfg
  | .error e =>
    throw <| IO.userError s!"invalid configuration: {e}"

public def run (cfg : CompilerConfig) : IO CompilerOutput := do
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[cfg.leanModule] .empty
    (leakEnv := true) (loadExts := true)
  let modIdx := env.getModuleIdx? cfg.leanModule |>.get!
  let some modCfg := modCfgExt.getStateByIdx? env modIdx |>.join
    | throw <| IO.userError "module lacks a Nerodia configuration"
  let mod : ModuleDef := {
    config := modCfg
    leanInit := Lean.mkModuleInitializationFunctionName cfg.leanModule (env.getModulePackageByIdx? modIdx)
    leanModule := cfg.leanModule
  }
  writeCFile cfg.cFile mod
  writePyiFile cfg.pyiFile mod
  return {
    name := modCfg.name
  }

public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [cfgFile] =>
      let out ← run (← readConfig cfgFile)
      IO.print (toJson out).pretty
      return (0 : UInt32)
    | [cfgFile, outFile] =>
      let out ← run (← readConfig cfgFile)
      IO.FS.writeFile outFile (toJson out).pretty
      return 0
    | _ =>
      IO.eprintln "USAGE: nerodiac <config.json> [<out.json>]"
      return 1
  catch e =>
    IO.eprintln e
    return 1
