import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]

/-! ## Python -/

structure PyConfig where
  exe : FilePath
  version : String
  hexVersion : Nat
  includeDirs : Array FilePath
  libDir : FilePath
  lib3 : String × FilePath
  lib3x : String × FilePath
  deriving ToJson, FromJson

instance : QueryText PyConfig := ⟨(toJson · |>.compress)⟩

input_file pyconfigSrc where
  text := true
  path := "pyconfig.py"

def minHexVersion : Nat := 0x030E00A0 -- 3.14 (a0)

target pyconfig : PyConfig := do
  (← pyconfigSrc.fetch).mapM fun srcFile => do
    let python3 := (← IO.getEnv "PYTHON3").getD <|
      -- `python3` aliases are not standard on Windows
      if System.Platform.isWindows then "python" else "python3"
    let out ← captureProc {cmd := python3, args := #[srcFile.toString]}
    match Json.parse out >>= fromJson? with
    | .ok py =>
      unless py.hexVersion ≥ minHexVersion do
        error s!"Nerodia requires Python 3.14+, got {py.version}"
      setTrace <| .ofHash
        (pureHash py.lib3.1) s!"pyconfig: {py.lib3.1}"
      return py
    | .error e =>
      error s!"configuration script produced unexpect output; {e}:\n{out}"

target libpython3 : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.lib3.1, path := py.lib3.2}

target libpython3x : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.lib3x.1, path := py.lib3x.2}

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
      s!"-DPy_LIMITED_API={minHexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile cJob weakArgs traceArgs cc getLeanTrace

/-! ## Nerodia Lean -/

@[default_target]
lean_lib Nerodia where
  defaultFacets := #[LeanLib.staticFacet]
  moreLinkObjs := #[nerodia.o]
  moreLinkLibs := #[libpython3]

@[default_target]
lean_lib Nerodia.Compiler where
  defaultFacets := #[LeanLib.staticFacet]

/-! ## Nerodiac -/

@[default_target]
lean_exe nerodiac where
  root := `Nerodiac
  supportInterpreter := true

structure NerodiacOutput where
  name : String
  c : FilePath
  o : FilePath
  pyi : FilePath

structure NerodiaConfig where
  name : String
  c : FilePath
  o : FilePath
  pyi : FilePath
  lib : FilePath
  libs : Array FilePath
  deriving ToJson

instance : QueryText NerodiaConfig := ⟨(toJson · |>.compress)⟩

structure CompilerConfig where
  leanModule : Lean.Name
  cFile : FilePath
  pyiFile : FilePath
  deriving ToJson, FromJson

structure CompilerOutput where
  name : String
  deriving ToJson, FromJson

def leanSharedDynlibs (lean : LeanInstall) : Array Dynlib :=
  -- libLake_shared links against the split libs on all platforms,
  -- so they must be included in the bundle even when they are empty stubs.
  if System.Platform.isWindows then
    -- On Windows, libraries are in `bin` and link to one another
    let init := {name := "Init_shared", path := lean.initSharedLib}
    let lean1 := {name := "leanshared_1", path := lean.binDir / s!"libleanshared_1.{sharedLibExt}", deps := #[init]}
    let lean2 := {name := "leanshared_2", path := lean.binDir / s!"libleanshared_2.{sharedLibExt}", deps := #[lean1, init]}
    let lean := {name := "leanshared", path := lean.sharedLib, deps := #[lean2, lean1, init]}
    #[lean, lean2, lean1, init]
  else
    -- On Unix, libraries are in `lean/lib` and are independent
    let init := {name := "Init_shared", path := lean.initSharedLib}
    let lean1 := {name := "leanshared_1", path := lean.leanLibDir / s!"libleanshared_1.{sharedLibExt}"}
    let lean2 := {name := "leanshared_2", path := lean.leanLibDir / s!"libleanshared_2.{sharedLibExt}"}
    let lean := {name := "leanshared", path := lean.sharedLib}
    #[lean, lean2, lean1, init]

-- Copied from `LeaneExe.recBuildExe`
def modLinks
  (mod : Module) (shouldExport : Bool)
: JobM (Array (Job FilePath) × Array (Job Dynlib)) := do
  /-
  Remark: We must build the root before we fetch the transitive imports
  so that errors in the import block of transitive imports will not kill this
  job before the root is built.
  -/
  let mut objJobs := #[]
  let mut libJobs := #[]
  for facet in mod.nativeFacets shouldExport do
    objJobs := objJobs.push <| ← facet.fetch mod
  let .ok imports _ ← (← mod.transImports.fetch).wait
    | error s!"bad imports (see the '{mod.name.toString}' job for details)"
  for mod in imports do
    for facet in mod.nativeFacets shouldExport do
      objJobs := objJobs.push <| ← facet.fetch mod
  for link in mod.lib.moreLinkObjs do
    objJobs := objJobs.push <| ← link.fetchIn mod.pkg
  let libs := imports.foldl (·.insert ·.lib) OrdHashSet.empty |>.toArray
  for lib in libs do
    for link in lib.moreLinkObjs do
      objJobs := objJobs.push <| ← link.fetchIn lib.pkg
    for link in lib.moreLinkLibs do
      libJobs := libJobs.push <| ← link.fetchIn lib.pkg
  for link in mod.lib.moreLinkLibs do
    libJobs := libJobs.push <| ← link.fetchIn mod.pkg
  let deps := (← (← mod.pkg.transDeps.fetch).await).push mod.pkg
  for dep in deps do
    for lib in dep.externLibs do
      objJobs := objJobs.push <| ← lib.static.fetch
  return (objJobs, libJobs)

module_facet nerodia (mod) : NerodiaConfig := do
  let cc := (← IO.getEnv "CC").getD "cc"
  let cFile := mod.irPath "nerodia.c"
  let oFile := mod.irPath "nerodia.o"
  let libFile := mod.irPath s!"nerodia.{sharedLibExt}"
  let pyiFile := mod.irPath "nerodia.pyi"
  let inFile := mod.irPath "nerodia.in.json"
  let outFile := mod.irPath "nerodia.out.json"
  let traceFile := mod.irPath "nerodia.trace"
  let pyJob ← pyconfig.fetch
  let modJob ← mod.leanArts.fetch
  let nerodiacJob ← nerodiac.fetch
  let libPyJob ← libpython3.fetch
  let (objJobs, libJobs) ← modLinks mod (shouldExport := true)
  -- Generate and compile extension
  let outJob ←
  modJob.bindM (sync := true) fun _ =>
  nerodiacJob.bindM (sync := true) fun nerodiac =>
  pyJob.mapM fun py => do
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
    let out ←
      match Json.parse (← IO.FS.readFile outFile) >>= fromJson? with
      | .ok (out : CompilerOutput) => pure out
      | .error e => error s!"nerodiac produced invalid output: {e}"
    -- `Py_LIMITED_API` must always be defined for abi3-tagged wheels
    let args := #[s!"-DPy_LIMITED_API={minHexVersion}", "-fPIC", "-std=c17"]
    addPureTrace args "traceArgs"
    addPlatformTrace -- object files are platform-dependent artifacts
    let art ← buildArtifactUnlessUpToDate oFile (ext := "o") do
      let args := args.push "-I" |>.push (← getLeanIncludeDir).toString
      let args := py.includeDirs.foldl (·.push "-I" |>.push ·.toString) args
      compileO oFile cFile args cc
    return {
      name := out.name
      c := cFile
      o := art.path
      pyi := pyiFile
      : NerodiacOutput
    }
  -- Link extension
  let traceArgs :=
    -- macOS requires `-undefined dynamic_lookup` so that Python C API symbols
    -- (provided by the interpreter at load time) don't cause link errors.
    if System.Platform.isOSX then #["-undefined", "dynamic_lookup"] else #[]
  -- Set RPATH so the extension finds bundled Lean shared libs in `.libs/`.
  let traceArgs :=
    if System.Platform.isWindows then traceArgs
    else if System.Platform.isOSX then traceArgs.push "-Wl,-rpath,@loader_path/.libs"
    else traceArgs.push "-Wl,-rpath,$ORIGIN/.libs"
  outJob.bindM (sync := true) fun out => do
    let lean ← getLeanInstall
    let lake ← getLakeInstall
    let dynlibs := leanSharedDynlibs lean
    let objs := #[Job.pure out.o] ++ objJobs
    let libs := libJobs ++ dynlibs.map Job.pure
    /-
    On Windows, all symbols must be resolved at link time.
    On Unix, Python symbols are provided by the interpreter at load time.
    Thus, on Unix, we need to exclude Python from the dependencies.

    TODO: Address trnasitive dependence on Python. As `libs` already flattens
    Lean libraries and their extra link dependencies, this can only happen if
    a extra link dependency itself depends on Python (via `Dynlib.deps`).
    -/
    let libs := if System.Platform.isWindows then libs else libs.filter fun job =>
      -- `ptrEq` works because Lake jobs are memoized
      ! unsafe ptrEq job libPyJob
    let libJob ← buildSharedLib out.name libFile
      objs libs lean.ccLinkSharedFlags traceArgs lean.cc.toString
      (linkDeps := true) -- extension should load deps when loaded in Python
      (extraDepTrace := getLeanTrace)
    libJob.bindM (sync := true) fun libFile =>
    return (Job.collectArray libs).map (sync := true) fun libs => {
      name := out.name
      c := out.c
      o := out.o
      pyi := out.pyi
      lib := libFile
      -- Lake is linked implicitly on an "as-needed" basis.
      -- Thus, it should be available in the bundle.
      libs := (libs ++ dynlibs).map (·.path) |>.push lake.sharedLib
    }

/--
Generates and builds Python extension modules from Lean modules.

USAGE:
  lake script run nerodia/buildExt <module-name>...

Generates the C code and `.pyi` type stub for each extension using `nerodiac`,
builds the Python extension shared library, and outputs a JSON description of
the results (a JSON object per line for each module). These descriptions can
then be used by `setuptools-lean` to bundle the extensions for distribution.
-/
script buildExt (args : List String) do
  if args.isEmpty then
    IO.println "USAGE: lake script run nerodia/buildExt <module-name>..."
    return 0
  let mods ← args.toArray.mapM fun modStr => do
    let modName := modStr.toName
    if modName.isAnonymous then
      error s!"invalid module name '{modStr}'"
    let some mod ← findModule? modName
      | error s!"unknown module '{modName}'"
    return mod
  let cfgs ← runBuild do
    Job.collectArray <$> mods.mapM fun mod =>
      mod.facet `nerodia |>.fetch
  for cfg in cfgs do
    IO.println (toJson cfg).compress
  return 0

/-! ## Nerodia Tests -/

lean_lib NerodiaTests where
  srcDir := "tests"
  globs := #[`NerodiaTests.+]
  precompileModules := true
  dynlibs :=
    -- On non-Windows, libpython3 = libpython3x
    if System.Platform.isWindows then #[libpython3x]
    else #[]

lean_exe testExe where
  srcDir := "tests"
  -- The Lean toolchain's sysroot may have an older glibc than the
  -- Python library, causing lld to reject unresolved versioned symbols.
  weakLinkArgs :=
    if System.Platform.isWindows || System.Platform.isOSX then #[]
    else #["-Wl,--allow-shlib-undefined"]

/--
Creates an virtual enviroment in `venvDir` that has the test Python package
named `pkg` located in `modDir` installed. Also ensures the `setuptools-lean`
dependency is installed from the appropriate source.
-/
def installPyPkg
  (pkg : String)
  (nerodiaDir modDir  : FilePath)
  (venvDir : FilePath := modDir / ".venv")
  (localSetuptoolsLean := true) (editable : Bool)
: JobM Unit := do
  proc {
      cmd := "uv",
      args := #["-q", "venv", "--clear", venvDir.toString]
      cwd := modDir
    }
  -- Ensures Python can find Lean's shared libraries
  -- Cannot include system libraries that will conflict with `cc`
  let libPath : SearchPath :=
    (← getLeanLibDir) :: (← getLakeEnv).initSharedLibPath
  let buildEnv := #[(sharedLibPathEnvVar, some libPath.toString)]
  if localSetuptoolsLean then
    proc {
      cmd := "uv"
      cwd := modDir
      args := #[
        "-q", "pip", "install", "--python", venvDir.toString,
        "-e", (nerodiaDir / "setuptools-lean").toString
      ]
    }
    proc {
      cmd := "uv"
      cwd := modDir
      env := buildEnv
      args :=
        if editable then #[
          "-q", "sync", "--python", venvDir.toString,
          "--no-build-isolation-package", pkg,
          "--reinstall-package", pkg
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
        if editable then #[
          "-q", "sync", "--python", venvDir.toString,
          "--default-index", "https://pypi.org/simple/",
          "--index", "https://test.pypi.org/simple/",
          "--index-strategy", "unsafe-first-match",
          "--reinstall-package", "setuptools-lean",
          "--reinstall-package", pkg
        ] else #[
          "-q", "pip", "install", "--python", venvDir.toString,
          "--default-index", "https://pypi.org/simple/",
          "--index", "https://test.pypi.org/simple/",
          "--index-strategy", "unsafe-first-match",
          "--reinstall-package", "setuptools-lean",
           ".",
        ]
    }

@[test_driver]
script test do
  let pkgDir := __dir__
  let testModuleDir := pkgDir / "tests" / "testModule"
  runBuild do
    let pyJob ← pyconfig.fetch
    let libJob ← Nerodia.fetch
    let nerodiacJob ← nerodiac.fetch
    discard <| NerodiaTests.fetch
    let exeJob ← testExe.fetch
    discard <| withRegisterJob "testExe test" do
      pyJob.bindM (sync := true) fun py =>
      exeJob.mapM fun exeFile => do
        let out ← captureProc {cmd := exeFile.toString, env := ← getPyEnv py}
        validateOutput py.version out
    let localSetuptoolsLean :=
      (← IO.getEnv "LOCAL_SETUPTOOLS_LEAN").bind envToBool? |>.getD false
    let editableVEnv := testModuleDir / ".venv"
    let nonEditableVEnv := testModuleDir / ".lake" / "dist-venv"
    let editableJob ← withRegisterJob "testModule editable install" do
      libJob.bindM (sync := true) fun _ =>
      nerodiacJob.mapM fun _ => do
        installPyPkg "test" pkgDir testModuleDir editableVEnv
          (editable := true) localSetuptoolsLean
    let nonEditableJob ← withRegisterJob "testModule non-editable install" do
      libJob.bindM (sync := true) fun _ =>
      nerodiacJob.mapM fun _ => do
        installPyPkg "test" pkgDir testModuleDir nonEditableVEnv
          (editable := false) localSetuptoolsLean
    discard <| withRegisterJob "testModule test" <| editableJob.mapM fun _ => do proc {
      cmd := "uv",
      args := #["-q", "run", "--python", editableVEnv.toString, "--no-sync", "test.py"]
      cwd := testModuleDir
      -- Ensures Python can find Lean's shared libraries
      env := ← getAugmentedEnv
    }
    discard <| withRegisterJob "testModule test (non-editable)" <| nonEditableJob.mapM fun _ => do proc {
      cmd := "uv",
      args := #[
        "-q", "run", "--python", nonEditableVEnv.toString, "--no-sync",
        -- Run from a different CWD with `-P` to ensure that Python is using the installed test module
        "python", "-P", testModuleDir / "test.py" |>.toString
      ]
      -- Non-editable installs bundle libraries, so it should run in a minimal environment.
      env := #[
        ("PATH", ← IO.getEnv "PATH"),
        ("HOME", ← IO.getEnv "HOME"),
        ("TMPDIR", ← IO.getEnv "TMPDIR"),
        ("UV_PYTHON_INSTALL_DIR", ← IO.getEnv "UV_PYTHON_INSTALL_DIR"),
        ("UV_CACHE_DIR", ← IO.getEnv "UV_CACHE_DIR"),
      ]
      inheritEnv := false
    }
    discard <| withRegisterJob "testModule ty" <| editableJob.mapM fun _ => do proc {
      cmd := "uvx",
      args := #["-q", "ty", "check", "-q", "test.py"]
      cwd := testModuleDir
    }
    withRegisterJob "testModule lpl" <| editableJob.mapM fun _ => do
      let out ← captureProc {
        cmd := "uv",
        args := #["run", "--no-sync", (← getLake).toString, "query", "--json", "lpl", "pyconfig"]
        cwd := testModuleDir
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
        cwd := testModuleDir
        env := ← getPyEnv pyconfig
      }
      validateOutput "Hello!" out
  return 0
where
  @[inline] validateOutput (expected actual : String) := do
    unless actual == expected do
      error s!"incorrect output: expected\
        \n  {expected}\
        \ngot\
        \n  {actual}"
  getPyEnv py := do
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
