/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]
  requiresModuleSystem := true

/-! ## Python -/

structure PyConfig where
  exe : FilePath
  version : String
  hexVersion : Nat
  freeThreaded : Bool
  includeDirs : Array FilePath
  libDir : FilePath
  lib3 : String × FilePath
  lib3x : String × FilePath
  isShared : Bool
  deriving ToJson, FromJson

instance : QueryText PyConfig := ⟨(toJson · |>.compress)⟩

input_file pyconfigSrc where
  text := true
  path := "pyconfig.py"

-- These must be kept in sync
abbrev pyTag : String := "cp314" -- CPython Limited API 3.14
abbrev abiTag : String := "abi3" -- Stable ABI (not free-threaded)
abbrev minHexVersion : Nat := 0x030E00A0 -- 3.14 (a0)
abbrev minPyVer : Nat := 14

target pyconfig : PyConfig := do
  (← pyconfigSrc.fetch).mapM fun srcFile => do
    let python3 := (← IO.getEnv "PYTHON3").getD <|
      -- `python3` aliases are not standard on Windows
      if System.Platform.isWindows then "python" else "python3"
    let out ← captureProc {cmd := python3, args := #[srcFile.toString]}
    match Json.parse out >>= fromJson? with
    | .ok py =>
      if py.freeThreaded then
        error s!"Nerodia does not support free-threaded Python, got:\
          \n  {py.version}"
      unless py.hexVersion ≥ minHexVersion do
        error s!"Nerodia requires Python 3.{minPyVer}+, got:\
          \n  {py.version}"
      unless py.isShared do
        -- TODO: Soften to linking executables and using `precompileModules`
        error s!"Nerodia requires a Python distribution with shared libraries, got:\
          \n  {py.lib3.2}"
      -- Use minimum Python in trace due to Stable ABI use, and
      -- rebuild only when library name changes due to host Python change.
      -- Other properties are constrained and thus cannot vary.
      let caption := s!"pyconfig: Python 3.{minPyVer}, {py.lib3.1}"
      let hash := (pureHash py.lib3.1).mix (pureHash minHexVersion)
      setTrace (.ofHash hash caption)
      return py
    | .error e =>
      error s!"configuration script produced unexpected output; {e}:\n{out}"

target libpython3x : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.lib3x.1, path := py.lib3x.2}

target libpython3 : Dynlib := do
  let cfgJob ← pyconfig.fetch
  let lib3xJob ← libpython3x.fetch
  lib3xJob.bindM (sync := true) fun lib3x => do
  return cfgJob.map (sync := true) fun py =>
    if py.lib3.1 == lib3x.name then
      {name := py.lib3.1, path := py.lib3.2}
    else -- Windows
      {name := py.lib3.1, path := py.lib3.2, runtimeOnlyDeps := #[lib3x]}

/-! ## Nerodia FFI -/

input_file nerodia.c where
  text := true
  path := "ffi" / "nerodia.c"

target nerodia.o pkg : FilePath := do
  let cJob ← nerodia.c.fetch
  (← pyconfig.fetch).bindM fun py => do
    newTrace
    let oFile := pkg.irDir / "c" / "nerodia.o"
    let weakArgs := py.includeDirs.map (s!"-I{·}")
      |>.push s!"-I{← getLeanIncludeDir}"
    let traceArgs := pkg.buildType.leancArgs ++ #[
      "-DLEAN_EXPORTING",
      s!"-DPy_LIMITED_API={minHexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile cJob weakArgs traceArgs cc getLeanTrace

/-! ## Nerodia Lean -/

@[default_target]
lean_lib Nerodia where
  -- Static for Python extensions and shared for precompilation
  defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]
  moreLinkObjs := #[nerodia.o]
  moreLinkLibs := #[libpython3]

-- Metaprograms used internally by Nerodia
lean_lib Nerodia.Internal where
  defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]

@[default_target]
lean_lib Nerodia.Compiler where
  defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]

-- Deliberately orphaned.
-- Its initializer creates a persistent Python environment.
lean_lib Nerodia.Test.Pure where
  defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]

/-! ## Nerodiac -/

@[default_target]
lean_exe nerodiac where
  root := `Nerodiac
  supportInterpreter := true

structure NerodiacOutput where
  name : String
  c : Artifact
  pyi : Artifact

structure CompilerConfig where
  leanModule : Lean.Name
  cFile : FilePath
  pyiFile : FilePath
  deriving ToJson

structure CompilerOutput where
  name : String
  deriving FromJson

module_facet nerodiacOut (mod) : NerodiacOutput := do
  let cFile := mod.irPath "nerodia.c"
  let pyiFile := mod.irPath "nerodia.pyi"
  let inFile := mod.irPath "nerodia.in.json"
  let outFile := mod.irPath "nerodia.out.json"
  let traceFile := mod.irPath "nerodia.trace"
  let modJob ← mod.leanArts.fetch
  let nerodiacJob ← nerodiac.fetch
  modJob.bindM (sync := true) fun _ =>
  nerodiacJob.mapM fun nerodiac => do
    addLeanTrace
    -- TODO: Build all outputs as artifacts
    buildUnlessUpToDate outFile (← getTrace) traceFile do
      let cfg : CompilerConfig := {
        leanModule := mod.name
        cFile, pyiFile
      }
      IO.FS.writeFile inFile (toJson cfg).compress
      proc {
        cmd := nerodiac.toString
        args := #[inFile.toString, outFile.toString]
        env := #[("LEAN_PATH", some (← getAugmentedLeanPath).toString)]
      }
      clearFileHash cFile
      clearFileHash pyiFile
    let out ←
      match Json.parse (← IO.FS.readFile outFile) >>= fromJson? with
      | .ok (out : CompilerOutput) => pure out
      | .error e => error s!"nerodiac produced invalid output: {e}"
    newTrace s!"{mod.name}:nerodiac"
    addPureTrace out.name "name"
    let c ← computeArtifact cFile "c" (text := true)
    addTrace c.trace
    let pyi ← computeArtifact pyiFile "pyi" (text := true)
    addTrace pyi.trace
    return {
      c, pyi
      name := out.name
      : NerodiacOutput
    }

module_facet nerodia.o (mod) : FilePath := do
  let pyJob ← pyconfig.fetch
  let nerodiacOut ← mod.facet `nerodiacOut |>.fetch
  nerodiacOut.bindM (sync := true) fun out =>
  pyJob.mapM fun py => do
    let cc := (← IO.getEnv "CC").getD "cc"
    let oFile := mod.irPath "nerodia.o"
    -- `Py_LIMITED_API` must always be defined for abi3-tagged wheels
    let args := #[s!"-DPy_LIMITED_API={minHexVersion}", "-fPIC", "-std=c17"]
    addLeanTrace
    addPureTrace args "traceArgs"
    addPlatformTrace -- object files are platform-dependent artifacts
    let art ← buildArtifactUnlessUpToDate oFile (ext := "o") do
      let args := args.push "-I" |>.push (← getLeanIncludeDir).toString
      let args := py.includeDirs.foldl (·.push "-I" |>.push ·.toString) args
      compileO oFile out.c.path args cc
    return art.path

structure ExtBuild where
  name : String
  pyi : FilePath
  lib : FilePath
  libs : Array FilePath
  deriving ToJson

instance : QueryText ExtBuild := ⟨(toJson · |>.compress)⟩

/--
Relative path from the Python extension to where the shared libs are stored.
Must stay in sync with the frontend (setuptools-lean) and the custom init test.
-/
abbrev libsDir : System.FilePath := "_lean.libs"

module_facet nerodiaExt (mod) : ExtBuild := do
  let libFile := mod.irPath s!"nerodia.{sharedLibExt}"
  let oJob ← mod.facet `nerodia.o |>.fetch
  let outJob ← mod.facet `nerodiacOut |>.fetch
  let libPyJob ← libpython3.fetch
  let linksJob ← mod.linkInfoExport.fetch
  oJob.bindM (sync := true) fun oFile => do
  outJob.bindM (sync := true) fun out => do
  libPyJob.bindM (sync := true) fun pyLib => do
  linksJob.mapM fun info => do
    let objs := info.objs.push oFile
    let lakeDynlib ← getLakeSharedDynlib
    let leanDynlibs ← getLeanSharedDynlibs
    -- Force Lean to link its shared libraries to the extension
    let libs := info.libs ++ leanDynlibs
    /-
    Extension-specific linker arguments:
    * Unix needs RPATH set so the extension finds bundled Lean shared libs
    in `libsDir`, whereas Windows uses dll directories set in the extension's
    `__init__.py`.
    * MacOS requires `-undefined dynamic_lookup` so that Python C API symbols
    (provided by the interpreter at load time) don't cause link errors.
    -/
    let extArgs :=
      if System.Platform.isWindows then
        #[]
      else if System.Platform.isOSX then
        #["-undefined", "dynamic_lookup", s!"-Wl,-rpath,@loader_path/{libsDir}"]
      else
        #[s!"-Wl,-rpath,$ORIGIN/{libsDir}"]
    addPureTrace extArgs "extArgs"
    let args := info.args ++ extArgs
    /-
    On Windows, all symbols must be resolved at link time.
    On Unix, Python symbols are provided by the interpreter at load time.
    Thus, we need to exclude Python from the link dependencies on Unix,
    and exclude it from the bundle list on both platforms.
    -/
    -- Eagerly flatten dep tree to build full list for Python
    let depLibs := (← mkLinkOrder libs).filter fun lib => lib.name != pyLib.name
    let linkLibs := if System.Platform.isWindows then libs else depLibs
    let libFile ← buildLeanSharedLibSync out.name libFile objs linkLibs args
      (linkDeps := true) -- extension should load deps when loaded in Python
    return {
      name := out.name
      pyi := out.pyi.path
      lib := libFile
      -- Lake is linked implicitly on an "as-needed" basis.
      -- Thus, it should be available in the bundle.
      libs := (depLibs.push lakeDynlib).map (·.path)
    }

/--
The components of a Python wheel tag.

Encoded as the standard Python tag triple (e.g., `["cp314", "abi3", "any"]`)
rather than as an object.
-/
structure WheelTag where
  py : String
  abi : String
  platform? : Option String := none -- unused

namespace WheelTag

protected def toJson (self : WheelTag) : Json :=
  Json.arr #[toJson self.py, toJson self.abi, toJson self.platform?]

instance : ToJson WheelTag := ⟨WheelTag.toJson⟩

protected def fromJson? (val : Json) : Except String WheelTag := do
  let arr ← val.getArr?
  if h : arr.size = 3 then
    return {
      py := ← fromJson? arr[0]
      abi := ← fromJson? arr[1]
      platform? := ← fromJson? arr[2]
    }
  else
    throw s!"expected a wheel tag triple, got {arr.size} elements"

instance : FromJson WheelTag := ⟨WheelTag.fromJson?⟩

end WheelTag

structure BackendConfig where
  /--
  Schema version of the frontend (setuptools-lean).
  Maximum version Nerodia can emit.
  -/
  -- not yet checked (only 1 public schema version)
  schemaVersion? : Option String
  /-- Minimum version the frontend supports. -/
  minSchemaVersion? : Option String
  /-- Wheel tag to target. If `none`, no tag is validated or reported. -/
  wheelTag? : Option WheelTag
  /-- Whether the package's source paths should be collected. -/
  collectSources : Bool
  /-- Lean modules for which to generate Python extensions. -/
  modules : Array String
  /-- Whether an extension build should actually be performed. -/
  build : Bool

protected def BackendConfig.fromJson? (val : Json) : Except String BackendConfig := do
  let obj ← JsonObject.fromJson? val
  return {
    schemaVersion? := ← obj.get? "schemaVersion"
    minSchemaVersion? := ← obj.get? "minSchemaVersion"
    wheelTag? := ← obj.get? "wheelTag"
    collectSources := ← obj.get "collectSources"
    modules := ← obj.getD "modules" #[]
    build := ← obj.get "build"
  }

instance : FromJson BackendConfig := ⟨BackendConfig.fromJson?⟩

def nerodiaSchemaVersion : Date :=
  {year := 2026, month := 07, day := 31}

-- Use native normalization rather than Lake's `/`-based instance.
-- Frontends like setuptools expect paths with native separators.
local instance : ToJson FilePath := ⟨(toJson ·.normalize)⟩ in
structure ExtDist where
  /--
  Schema version Nerodia emits.
  Minimum of the configuration `schemaVersion` and `nerodiaSchemaVersion`.
  -/
  schemaVersion : Date
  /-- Wheel tag Nerodia targets. `none` if the configuration had no tag. -/
  wheelTag? : Option WheelTag
  /-- Built extension modules. -/
  builds : Array ExtBuild
  /--
  Absolute paths to the Lean sources of the root package.

  The frontend (setuptools-lean) can include these in the source distribution
  by default, so that it carries everything Lake needs to rebuild.
  -/
  srcPaths : Array FilePath
  deriving ToJson

/--
Collects the absolute paths to the sources of the package:
* The Lake configuration, manifest, and `lean-toolchain`
* Files specified by `input_file`  and `input_dir` targets
* Roots of each `lean_lib` and their submodule directories
* The source of the root module of each `lean_exe`.

A library contributes its roots rather than its whole `srcDir` because
`srcDir` defaults to the package directory, which also holds build output
and unrelated files (e.g., the Python package the extension is bundled into).
-/
def getSrcPaths (pkg : Package) : IO (Array FilePath) := do
  let mut paths : OrdHashSet FilePath := addFiles .empty
    #[pkg.configFile, pkg.manifestFile]
  paths ← addFileIfExists paths <| pkg.dir / "lean-toolchain"
  for decl in pkg.targetDecls do
    match decl.kind with
    | InputFile.configKind =>
      if let some input := pkg.findConfigTarget? InputFile.configKind decl.name then
        paths := addFile paths (InputFile.path input)
    | InputDir.configKind =>
      if let some input := pkg.findConfigTarget? InputDir.configKind decl.name then
        paths ← addDir paths (InputDir.path input) (InputDir.filter input)
    | LeanLib.configKind =>
      if let some lib := pkg.findConfigTarget? LeanLib.configKind decl.name then
        let srcDir := LeanLib.srcDir lib
        for root in (LeanLib.config lib).roots do
          -- A root need not exist (e.g., a library globbing only submodules).
          paths ← addFileIfExists paths (Lean.modToFilePath srcDir root "lean")
          paths ← addDir paths (Lean.modToFilePath srcDir root "")
    | LeanExe.configKind =>
      if let some exe := pkg.findConfigTarget? LeanExe.configKind decl.name then
        paths := addFile paths (LeanExe.root exe).leanFile
    | _ => pure ()
  return paths.toArray
where
  @[inline] addFile paths (file : FilePath) :=
    paths.insert file
  @[inline] addFileIfExists paths (file : FilePath) :=
    return if ← file.pathExists then addFile paths file else paths
  addFiles paths (files : Array FilePath) :=
    files.foldl addFile paths -- specializes `foldl`
  addDir paths dir (filter := fun _ => true) := do
    unless ← dir.isDir do
      return paths
    (← dir.walkDir).foldlM (init := paths) fun paths file => do
      return if filter file && !(← file.isDir) then addFile paths file else paths

/--
Generates Python extension modules from Lean modules for distribution.

USAGE:
  lake script run nerodia/preparePyDist

Receives a JSON configuration through standard input and outputs a JSON
description of the results.

When the configuration sets a `wheelTag`, Nerodia validates that it supports it
and returns the wheel tag Nerodia would prefer.

When the configuration sets `collectSources := true`, Nerodia produces an
array of absolute paths to the sources of targets Nerodia understands:
`lean_lib`, `lean_exe`, `input_file`, `input_dir`.

When the configuration sets `build := true`, Nerodia generates the C code and
the `.pyi` type stub  for each extension using `nerodiac`, and builds the
Python extension shared library.

The Python plugin `setuptools-lean` uses this script to create both source
and binary distributions.
-/
script preparePyDist do
  let input ← (← IO.getStdin).readToEnd
  let cfg ← id do
    match Json.parse input >>= fromJson? with
    | .ok (cfg : BackendConfig) => return cfg
    | .error e => error s!"invalid configuration; {e}:\n{input}"
  if let some minVer := cfg.minSchemaVersion? then
    if let some date := Date.ofString? minVer then
      if nerodiaSchemaVersion < date then
        error s!"configuration requires schema version {minVer}, \
          but this version of Nerodia only supports up to {nerodiaSchemaVersion}"
    else
      error s!"unknown minimum configuration schema: {minVer}"
  if let some cfgTag := cfg.wheelTag? then
    if let some cpVer := cfgTag.py.dropPrefix? "cp3" >>= (·.toNat?) then
      if cpVer < minPyVer then
        error s!"Nerodia requires CPython 3.{minPyVer}+, got 3.{cpVer}"
    else
      error s!"Nerodia requires CPython 3.{minPyVer}+, got {cfgTag.py}"
    if let some cpVer := cfgTag.abi.dropPrefix? "cp3" >>= (·.toNat?) then
      if cpVer < minPyVer then
        error s!"Nerodia requires Limited API 3.{minPyVer}+, got 3.{cpVer}"
    else if cfgTag.abi != "abi3" then
      error s!"Nerodia requires Limited API 3.{minPyVer}+, got {cfgTag.abi}"
  -- Collect source paths
  let srcPaths ← id do
    if cfg.collectSources then
      getSrcPaths (← getWorkspace).root
    else
      return #[]
  -- always validate module names, even if no build occurs
  let mods ← cfg.modules.mapM fun modStr => do
    let modName := modStr.toName
    if modName.isAnonymous then
      error s!"invalid module name '{modStr}'"
    let some mod ← findModule? modName
      | error s!"unknown module '{modName}'"
    return mod
  let builds ← id do
    if cfg.build then
      runBuild <| Job.collectArray <$> mods.mapM fun mod =>
        mod.facet `nerodiaExt |>.fetch
    else
      return #[]
  let dist : ExtDist := {
    builds, srcPaths
    schemaVersion := nerodiaSchemaVersion
    wheelTag? := cfg.wheelTag?.map fun _ => {py := pyTag, abi := abiTag}
  }
  IO.println (toJson dist).compress
  return 0

/-! ## Nerodia Tests -/

lean_lib NerodiaTests where
  srcDir := "tests"
  globs := #[`NerodiaTests.+]
  precompileModules := true
  allowNonModules := true

lean_exe pyInExe where
  srcDir := "tests"
  -- The Lean toolchain's sysroot may have an older glibc than the
  -- Python library, causing lld to reject unresolved versioned symbols.
  weakLinkArgs :=
    if System.Platform.isWindows || System.Platform.isOSX then #[]
    else #["-Wl,--allow-shlib-undefined"]

/--
Arguments that opt a test package's build into `setuptools-lean` prereleases.

uv 0.12 prefers stable releases and `--prerelease` does not apply to build
requirements, so a constraint is the only way to use prereleases.
-/
def pyPrereleaseArgs (modDir : FilePath) : Array String := #[
  "--default-index", "https://pypi.org/simple/",
  "--index", "https://test.pypi.org/simple/",
  "--index-strategy", "unsafe-first-match",
  "--build-constraints", (modDir / ".." / "build-constraints.txt").toString
]

/--
Environment for a Python build that invokes Lake.

Ensures Python can find Lean's shared libraries.
Cannot include system libraries that will conflict with `cc`.
-/
def getPyBuildEnv : JobM (Array (String × Option String)) := do
  let libPath : SearchPath :=
    (← getLeanLibDir) :: (← getLakeEnv).initSharedLibPath
  return #[(sharedLibPathEnvVar, some libPath.toString)]

/--
Creates a virtual environment in `venvDir` that has the test Python package
located in `modDir` installed. Also ensures the `setuptools-lean` dependency
is installed from the appropriate source.
-/
def installPyPkg
  (modDir : FilePath)
  (venvDir : FilePath := modDir / ".venv")
  (localSetuptoolsLean? : Option FilePath := none)
  (editable : Bool)
: JobM Unit := do
  proc {
      cmd := "uv",
      args := #["-q", "venv", "--clear", venvDir.toString]
      cwd := modDir
    }
  let buildEnv ← getPyBuildEnv
  if let some pluginDir := localSetuptoolsLean? then
    proc {
      cmd := "uv"
      cwd := modDir
      args := #[
        "-q", "pip", "install", "--python", venvDir.toString,
        "-e", pluginDir.toString
      ]
    }
    proc {
      cmd := "uv"
      cwd := modDir
      env := buildEnv
      args :=
        if editable then #[
          "-q", "pip", "install", "--python", venvDir.toString,
          "--no-build-isolation", "-e", "."
        ] else #[
          "-q", "pip", "install", "--python", venvDir.toString,
          "--no-build-isolation", "."
        ]

    }
  else
    proc {
      cmd := "uv"
      cwd := modDir
      env := buildEnv
      args :=
        #["-q", "pip", "install", "--python", venvDir.toString]
        ++ pyPrereleaseArgs modDir
        ++ #["--reinstall-package", "setuptools-lean"]
        ++ (if editable then #["-e", "."] else #["."])
    }

@[inline] def validateOutput
  [Monad m] [MonadError m] (expected actual : String)
 : m PUnit := do
  unless actual == expected do
    error s!"incorrect output: expected\
      \n  {expected}\
      \ngot\
      \n  {actual}"

def getPyEnv (py : PyConfig) : JobM (Array (String × Option String)) := do
    -- Ensures the executable can find Lean and Python's shared libraries
    let libPath ← getAugmentedSharedLibPath
    let libPath : SearchPath := py.libDir :: libPath
    return #[
      (sharedLibPathEnvVar, some libPath.toString),
      -- Activate the venv for embedded Python if necessary
      -- Normalized for Windows: CPython's `getpath` only splits on backslashes,
      -- so a forward-slash path breaks venv detection (fatal as of 3.14)
      ("__PYVENV_LAUNCHER__", some py.exe.normalize.toString),
    ]

def testEditable
  (venvDir modDir : FilePath) (relTest : FilePath := "test.py")
: JobM Unit := do proc {
  cmd := "uv"
  cwd := modDir
  args := #["-q", "run", "--python", venvDir.toString, "--no-sync", relTest.toString]
  -- Ensures Python can find Lean's shared libraries
  env := ← getAugmentedEnv
}

def testNonEditable
  (venvDir modDir : FilePath) (relTest : FilePath := "test.py")
: JobM Unit := do proc {
  cmd := "uv"
  args := #[
    "-q", "run", "--python", venvDir.toString, "--no-sync",
    -- Run from a different CWD with `-P` to ensure that Python is using the installed test module
    "python", "-P", (modDir / relTest).toString
  ]
  -- Non-editable installs bundle libraries, so it should run in a minimal environment.
  env := #[
    ("PATH", ← IO.getEnv "PATH"),
    ("HOME", ← IO.getEnv "HOME"),
    ("TMPDIR", ← IO.getEnv "TMPDIR"),
    ("UV_PYTHON_INSTALL_DIR", ← IO.getEnv "UV_PYTHON_INSTALL_DIR"),
    ("UV_CACHE_DIR", ← IO.getEnv "UV_CACHE_DIR"),
  ]
}

def testTypeCheck
  (venvDir modDir : FilePath) (relTest : FilePath := "test.py")
: JobM Unit := do proc {
  cmd := "uvx"
  args := #[
    "-q", "ty", "check", "-q",
    "--python", venvDir.toString, (modDir / relTest).toString
  ]
}

def testLPL (venvDir modDir : FilePath) : JobM Unit := do
  let out ← captureProc {
    cmd := "uv"
    cwd := modDir
    args := #[
      "run", "--python", venvDir.toString, "--no-sync",
      (← getLake).toString, "query", "--json", "lpl", "pyconfig"
    ]
    -- Ensures Python can find Lean's shared libraries
    env := ← getAugmentedEnv
  }
  let [lpl, pyconfig] := out.lines.toStringList
    | error s!"unexpected lake output: {out}"
  let lpl ← match Json.parse lpl >>= fromJson? with
    | .ok a => pure a
    | .error e => error s!"invalid executable path; {e}:\n{out}"
  let pyconfig ← match Json.parse pyconfig >>= fromJson? with
    | .ok a => pure a
    | .error e => error s!"invalid python configuration; {e}:\n{out}"
  let out ← captureProc {
    cmd := lpl,
    cwd := modDir
    env := ← getPyEnv pyconfig
  }
  validateOutput "Hello!" out

/--
Builds a source distribution of the test package and validates its contents.

The sdist is not installed: the test packages require `nerodia` through a path
dependency on the repository, so their source distributions are not installable.
-/
def testSdist
  (venvDir modDir : FilePath) (localSetuptoolsLean? : Option FilePath)
: JobM Unit := do
  let outDir := modDir / ".lake" / "sdist"
  -- Without this, `manifest_maker` reuses the `SOURCES.txt` of an earlier
  -- build, so sources the backend stops reporting still ship. If this is
  -- removed, verify a sdist built twice in a row still omits them.
  for entry in ← modDir.readDir do
    if entry.fileName.endsWith ".egg-info" then
      IO.FS.removeDirAll entry.path
  let buildArgs := #[
    "-q", "build", "--sdist", "--clear", "--no-create-gitignore",
    "--out-dir", outDir.toString, "--python", venvDir.toString
  ]
  proc {
    cmd := "uv"
    cwd := modDir
    env := ← getPyBuildEnv
    args :=
      if localSetuptoolsLean?.isSome then
        -- The venv already has the local `setuptools-lean` and `setuptools`.
        buildArgs.push "--no-build-isolation"
      else
        buildArgs ++ pyPrereleaseArgs modDir
          ++ #["--refresh-package", "setuptools-lean"]
  }
  let expectedFile := modDir / ".lake" / "sdist-expected.json"
  let expected := (← getSdistPaths modDir).map (·.toString)
  IO.FS.writeFile expectedFile (toJson expected).pretty
  proc {
    cmd := "uv"
    cwd := modDir
    args := #[
      "-q", "run", "--python", venvDir.toString, "--no-sync",
      "python", "-P", (modDir / ".." / "check_sdist.py").toString,
      modDir.toString, outDir.toString, expectedFile.toString
    ]
  }
where
  /-- Returns the test module paths expected to be in the source distribution. -/
  getSdistPaths (modDir : FilePath) : IO (Array FilePath) := do
    let excluded := #[".lake", ".venv", "build", "__pycache__"]
    let included := #["lean-toolchain" , "lakefile.toml",  "lake-manifest.json" ]
    let entries ← modDir.walkDir fun dir => do
      let some name := dir.fileName
        | return true -- enter a root (e.g., `/`)
      return !excluded.contains name && !name.endsWith ".egg-info"
    entries.filterMapM fun path => do
      let some name := path.fileName
        | return none -- only directories can lack file names
      -- `lakefile.lean` is covered by extension rather than inclusion
      unless path.extension == some "lean" || included.contains name do
        return none
      if ← path.isDir then
        return none
      return some path

def testModule
  (testName : String) (modDir : FilePath) (localSetuptoolsLean? : Option FilePath)
: FetchM Unit := do
  let editableVEnv := modDir / ".venv"
  let nonEditableVEnv := modDir / ".lake" / "dist-venv"
  -- The editable and non-editable installs cannot be run in parallel.
  -- Neither uv nor setuptools ensures thread safe access to `*.egg-info`.
  let editableJob ← withRegisterJob s!"{testName} editable install" <| Job.async do
    installPyPkg modDir editableVEnv
      (editable := true) localSetuptoolsLean?
  let nonEditableJob ← withRegisterJob s!"{testName} non-editable install" do
    editableJob.mapM fun _ =>
      installPyPkg modDir nonEditableVEnv
        (editable := false) localSetuptoolsLean?
  discard <| withRegisterJob s!"{testName} test (editable)" do
    editableJob.mapM fun _ =>
      testEditable editableVEnv modDir
  discard <| withRegisterJob s!"{testName} test (non-editable)" do
    nonEditableJob.mapM fun _ => do
      testNonEditable nonEditableVEnv modDir
  discard <| withRegisterJob s!"{testName} ty" do
    editableJob.mapM fun _ =>
      testTypeCheck editableVEnv modDir
  -- Serialized with the installs: it also writes `*.egg-info`.
  discard <| withRegisterJob s!"{testName} sdist" do
    nonEditableJob.mapM fun _ =>
      testSdist editableVEnv modDir localSetuptoolsLean?
  if ← (modDir / "lpl.lean").pathExists then
    discard <| withRegisterJob s!"{testName} lpl" do
      editableJob.mapM fun _ =>
        testLPL editableVEnv modDir

def getLocalSetuptoolsLean? : IO (Option FilePath) := OptionT.run do
  IO.FS.realPath (← OptionT.mk <| IO.getEnv "SETUPTOOLS_LEAN")

@[test_driver]
script test do
  let pkgDir := __dir__
  let localSetuptoolsLean? ← getLocalSetuptoolsLean?
  runBuild do
    let pyJob ← pyconfig.fetch
    let libJob ← Nerodia.fetch
    let nerodiacJob ← nerodiac.fetch
    -- Lean tests
    discard <| NerodiaTests.fetch
    discard <| withRegisterJob "pyInExe test" do
      let exeJob ← pyInExe.fetch
      pyJob.bindM (sync := true) fun py =>
      exeJob.mapM fun exeFile => do
        let out ← captureProc {cmd := exeFile.toString, env := ← getPyEnv py}
        validateOutput py.version out
    -- Python extension module tests
    libJob.bindM (sync := true) fun _ =>
    nerodiacJob.mapM fun _ => do
      for e in ← pkgDir / "tests" / "lean2py" |>.readDir do
        if ← e.path.isDir then
          testModule s!"lean2py/{e.fileName}" e.path localSetuptoolsLean?
  return 0
