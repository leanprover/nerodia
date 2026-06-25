/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
*/
#include <Python.h>
#include <lean/lean.h>
#include <stdatomic.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#endif

/* ## Python Mutex */

#ifdef _WIN32
static CRITICAL_SECTION g_py_mutex;
static INIT_ONCE g_py_mutex_once = INIT_ONCE_STATIC_INIT;
static BOOL CALLBACK py_init_mutex(PINIT_ONCE once, PVOID param, PVOID *ctx) {
  InitializeCriticalSection(&g_py_mutex);
  return TRUE;
}
#define py_mutex_lock()   (InitOnceExecuteOnce(&g_py_mutex_once, py_init_mutex, NULL, NULL), \
                           EnterCriticalSection(&g_py_mutex))
#define py_mutex_unlock() LeaveCriticalSection(&g_py_mutex)
#else
static pthread_mutex_t g_py_mutex = PTHREAD_MUTEX_INITIALIZER;
#define py_mutex_lock()   pthread_mutex_lock(&g_py_mutex)
#define py_mutex_unlock() pthread_mutex_unlock(&g_py_mutex)
#endif

/* ## Basics */

static void nop_foreach(void* p, b_lean_obj_arg f) {
  return;
}

typedef struct {
  bool is_held;
  atomic_int holders;
  bool is_initializer;
} py_environment;

static py_environment g_py_env = {
  .is_held = false,
  .holders = 0,
};

typedef struct {
  bool is_held;
  atomic_int holders;
  PyGILState_STATE gil;
} py_context;

static _Thread_local py_context g_py_ctx = {
  .is_held = false,
  .holders = 0,
};

static lean_external_class* g_py_context_external_class = NULL;
static lean_external_class* g_py_object_external_class = NULL;

static inline void py_finalize(PyGILState_STATE gil) {
  // `g_py_env.holders > 0` implies we raced with the environment initializer,
  // they acquired the lock first, and they want the environment alive.
  if (atomic_load(&g_py_env.holders) == 0) {
    g_py_env.is_held = false;
    if (g_py_env.is_initializer) {
      Py_Finalize();
      return;
    }
  }
  PyGILState_Release(gil);
}

static void py_context_foreach(void* p, b_lean_obj_arg f) {
  lean_internal_panic(
    "`PyContext` marked persistent or multi-threaded. "
    "This is forbidden as `PyContext` holds the Python GIL.");
}

static void py_context_finalize(void* p) {
  if (atomic_fetch_sub(&g_py_ctx.holders, 1) == 1) {
    py_mutex_lock();
    // `g_py_ctx.holders > 0` implies we raced with the context initializer,
    // they acquired the lock first, and they want the context alive.
    if (atomic_load(&g_py_ctx.holders) == 0) {
      g_py_ctx.is_held = false;
      if (atomic_fetch_sub(&g_py_env.holders, 1) == 1) {
        py_finalize(g_py_ctx.gil);
      } else {
        PyGILState_Release(g_py_ctx.gil);
      }
    }
    py_mutex_unlock();
  }
}

static void py_object_finalize(void* p) {
  PyGILState_STATE gil = PyGILState_Ensure();
  Py_DECREF(p);
  PyGILState_Release(gil);
  if (atomic_fetch_sub(&g_py_env.holders, 1) == 1) {
    // no env holders implies no context holders either
    py_mutex_lock();
    py_finalize(PyGILState_Ensure());
    py_mutex_unlock();
  }
}

static inline void nerodia_ctx_of_env(void) {
  if (atomic_fetch_add(&g_py_ctx.holders, 1) == 0) {
    // `g_py_ctx.is_held = true` implies we raced with the context finalizer,
    // we acquired the lock first, and thus we can simply reuse the context.
    if (!g_py_ctx.is_held) {
      g_py_ctx.is_held = true;
      g_py_ctx.gil = PyGILState_Ensure();
      atomic_fetch_add(&g_py_env.holders, 1);
    }
  }
}

/* init :  BaseIO PyContext */
LEAN_EXPORT lean_obj_res nerodia_py_context_init(void) {
  py_mutex_lock();
  if (g_py_env.is_held) {
    nerodia_ctx_of_env();
    py_mutex_unlock();
    return lean_alloc_external(g_py_context_external_class, NULL);
  }
  if (!g_py_context_external_class) {
    g_py_context_external_class = lean_register_external_class(
      py_context_finalize, py_context_foreach);
  }
  if (!g_py_object_external_class) {
    g_py_object_external_class = lean_register_external_class(
      py_object_finalize, nop_foreach);
  }
  if (Py_IsInitialized()) {
    g_py_env.is_initializer = false;
  } else {
    g_py_env.is_initializer = true;
    Py_Initialize();
    // Release the initial GIL and discard the main thread state.
    // Note: Ideally, we could save the main thread state and restore it in
    // `py_finalize`. However, there is no clear way to ensure both happen in
    // the same thread, so we take this approach instead.
    PyEval_SaveThread();
  }
  g_py_env.is_held = true;
  atomic_store(&g_py_env.holders, 1);
  g_py_ctx.is_held = true;
  atomic_store(&g_py_ctx.holders, 1);
  g_py_ctx.gil = PyGILState_Ensure();
  py_mutex_unlock();
  return lean_alloc_external(g_py_context_external_class, NULL);
}

lean_obj_res nerodia_of_object_core(PyObject* o) {
  return lean_alloc_external(g_py_object_external_class, o);
}

static inline lean_obj_res nerodia_of_object(PyObject* o, b_lean_obj_arg ctx) {
  // convert reference to `ctx` to a global reference to the Python environment
  atomic_fetch_add(&g_py_env.holders, 1);
  return nerodia_of_object_core(o);
}

static inline lean_obj_res nerodia_of_immortal_object(PyObject* o, b_lean_obj_arg ctx) {
  // Note: Python 3.13+ allows references to immortal objects (e.g., types)
  // to be decremented without an increment, so we can avoid one here.
  return nerodia_of_object(o, ctx);
}

static inline PyObject* nerodia_to_object(b_lean_obj_arg o) {
  assert(lean_get_external_class(o) == g_py_object_external_class);
  return (PyObject*)lean_get_external_data(o);
}

static inline PyTypeObject* nerodia_to_type_object(b_lean_obj_arg o) {
  return (PyTypeObject*)nerodia_to_object(o);
}

/* ## Python C Extension API */

#ifdef _WIN32
static CRITICAL_SECTION g_lean_mutex;
static INIT_ONCE g_lean_mutex_once = INIT_ONCE_STATIC_INIT;
static BOOL CALLBACK lean_init_mutex(PINIT_ONCE once, PVOID param, PVOID *ctx) {
  InitializeCriticalSection(&g_lean_mutex);
  return TRUE;
}
#define lean_mutex_lock()   (InitOnceExecuteOnce(&g_lean_mutex_once, lean_init_mutex, NULL, NULL), \
                           EnterCriticalSection(&g_lean_mutex))
#define lean_mutex_unlock() LeaveCriticalSection(&g_lean_mutex)
#else
static pthread_mutex_t g_lean_mutex = PTHREAD_MUTEX_INITIALIZER;
#define lean_mutex_lock()   pthread_mutex_lock(&g_lean_mutex)
#define lean_mutex_unlock() pthread_mutex_unlock(&g_lean_mutex)
#endif

void lean_initialize(void);
uint8_t lean_io_initializing(void);
lean_obj_res nerodia_internal_set_init(uint8_t init);

/** Initializes Nerodia for use in a Python extension.  */
LEAN_EXPORT void nerodia_initialize_lean(void) {
  // Remark: This function many be called from multiple Lean extension imports,
  // or if Lean code imports a Python module which imports Lean code, so it must
  // be idempotent and race-free in all cases.
  lean_mutex_lock();
  if (lean_io_initializing()) {
    // Remark: Consider use of `lean_setup_args` via `Py_GetArgcArgv`.
    // However, it is not clear whether there is a good way to keep them in sync.
    lean_initialize();
    lean_init_task_manager();
    lean_io_mark_end_initialization();
  }
  nerodia_internal_set_init(true);
}

/** Marks the end of Nerodia initialization from Python. */
LEAN_EXPORT void nerodia_mark_end_initialization(void) {
  nerodia_internal_set_init(false);
  // Remark: Must hold mutex until here to avoid races on the `Lean.initializing` flag.
  lean_mutex_unlock();
}

lean_obj_res lean_io_error_to_string(lean_obj_arg e);

/** Sets a Python exeception on an Lean module initialization failure.  */
LEAN_EXPORT void nerodia_set_init_error(lean_obj_arg init_res, const char *mod_name) {
  lean_object* err = lean_io_result_get_error(init_res);
  lean_inc_ref(err);
  lean_dec_ref(init_res);
  err = lean_io_error_to_string(err);
  PyErr_Format(PyExc_ImportError, // TODO: Error class for Lean errors
    "Failed to initialize Lean module '%s': %s",
    mod_name, lean_string_cstr(err));
  lean_dec_ref(err);
}
/* ## Lean API */

LEAN_EXPORT size_t nerodia_py_object_addr(b_lean_obj_arg self) {
  return (size_t)nerodia_to_object(self);
}

LEAN_EXPORT size_t nerodia_py_object_new_ref(b_lean_obj_arg self) {
  return (size_t)Py_NewRef(nerodia_to_object(self));
}

LEAN_EXPORT lean_obj_res nerodia_py_object_ctx(b_lean_obj_arg self) {
  py_mutex_lock();
  // self implies `g_py_env` exists
  nerodia_ctx_of_env();
  py_mutex_unlock();
  return lean_alloc_external(g_py_context_external_class, NULL);
}

/* mkObject : @& PyContext -> (ptr : CPtr α) -> ¬ ptr.IsNull -> α */
LEAN_EXPORT lean_obj_res nerodia_py_context_mk_object(b_lean_obj_arg ctx, size_t ptr) {
  return nerodia_of_object((PyObject*)ptr, ctx);
}

/* mkObjectRef : @& PyContext -> (ptr : CPtr α) -> ¬ ptr.IsNull -> α */
LEAN_EXPORT lean_obj_res nerodia_py_context_mk_object_ref(b_lean_obj_arg ctx, size_t ptr) {
  return nerodia_of_object(Py_NewRef((PyObject*)ptr), ctx);
}

/* mkArgsUnsafe : @& PyContext -> CPyArgs -> USize -> Array PyObject */
LEAN_EXPORT lean_obj_res nerodia_py_context_mk_args(b_lean_obj_arg ctx, size_t args, size_t nargs) {
  lean_obj_res objs = lean_alloc_array(nargs, nargs);
  for (size_t i = 0; i < nargs; ++i) {
    lean_array_set_core(objs, i,
      nerodia_of_object(Py_NewRef(((PyObject**)args)[i]), ctx));
  }
  return objs;
}

/* mkNthArgUnsafe : @& PyContext -> CPyArgs -> USize -> PyObject */
LEAN_EXPORT lean_obj_res nerodia_py_context_mk_nth_arg(b_lean_obj_arg ctx, size_t args, size_t i) {
  return nerodia_of_object(Py_NewRef(((PyObject**)args)[i]), ctx);
}

/* clearError : @& PyContext -> BaseIO Unit */
LEAN_EXPORT lean_obj_res nerodia_py_context_clear_error(b_lean_obj_arg ctx) {
  PyErr_Clear();
  return lean_box(0);
}

/* getRaisedException : CPyIO PyBaseException */
LEAN_EXPORT size_t nerodia_get_raised_exception() {
  return (size_t)PyErr_GetRaisedException();
}

/* CPtr PyBaseException -> BaseIO Unit */
LEAN_EXPORT lean_obj_res nerodia_set_raised_exception(size_t e) {
  PyErr_SetRaisedException((PyObject*)e);
  return lean_box(0);
}

/* @& String -> BaseIO α */
LEAN_EXPORT lean_obj_res nerodia_set_py_type_error(b_lean_obj_arg msg) {
  PyErr_SetString(PyExc_TypeError, lean_string_cstr(msg));
  return lean_box(0);
}

LEAN_NORETURN void nerodia_exception_panic() {
  if (PyErr_ExceptionMatches(PyExc_MemoryError)) {
    lean_internal_panic_out_of_memory();
  } else {
    PyErr_WriteUnraisable(NULL);
    lean_internal_panic_unreachable();
  }
}

/* @& String -> @& PyContext -> PySystemError */
LEAN_EXPORT lean_obj_res nerodia_py_context_system_error(b_lean_obj_arg msg, b_lean_obj_arg ctx) {
  PyObject* msg_obj = PyUnicode_FromString(lean_string_cstr(msg));
  if (LEAN_LIKELY(msg != NULL)) {
    PyObject* ex = PyObject_CallFunctionObjArgs(
      PyExc_SystemError, msg_obj, NULL);
    Py_DECREF(msg_obj);
    if (LEAN_LIKELY(ex != NULL)) {
      return nerodia_of_object(ex, ctx);
    }
  }
  nerodia_exception_panic();
}


LEAN_EXPORT lean_obj_res nerodia_py_context_none(b_lean_obj_arg ctx) {
  return nerodia_of_immortal_object(Py_None, ctx);
}

/* import : @& String -> BaseIO (CPtr PyObject) */
LEAN_EXPORT size_t nerodia_import(b_lean_obj_arg mod_name) {
  return (size_t)PyImport_ImportModule(lean_string_cstr(mod_name));
}

/* addByString : @& String -> @& PyObject -> @& Module -> CPyUnitIO */
LEAN_EXPORT int32_t nerodia_py_module_add_by_string
  (b_lean_obj_arg name, b_lean_obj_arg val, b_lean_obj_arg mod)
{
  return PyModule_AddObjectRef(nerodia_to_object(mod),
    lean_string_cstr(name), nerodia_to_object(val));
}

/* getAttrByString : @& String -> BaseIO (CPtr PyObject) */
LEAN_EXPORT size_t nerodia_py_object_get_attr_by_string(b_lean_obj_arg self, b_lean_obj_arg attr_name) {
  return (size_t)PyObject_GetAttrString(nerodia_to_object(self), lean_string_cstr(attr_name));
}

/* ### Types */

/** getType : @& PyObject -> PyBaseIO PyType  */
LEAN_EXPORT lean_obj_res nerodia_py_object_get_type(b_lean_obj_arg self, b_lean_obj_arg ctx) {
  PyObject* ty = Py_NewRef((PyObject*)Py_TYPE(nerodia_to_object(self)));
  return nerodia_of_object(ty, ctx);
}

LEAN_EXPORT uint8_t nerodia_py_object_is_type_instance(b_lean_obj_arg self) {
  return PyType_Check(nerodia_to_object(self)) != 0;
}

LEAN_EXPORT uint8_t nerodia_py_object_is_str_instance(b_lean_obj_arg self) {
  return PyUnicode_Check(nerodia_to_object(self)) != 0;
}

LEAN_EXPORT lean_obj_res nerodia_py_context_type_type(b_lean_obj_arg ctx) {
  return nerodia_of_immortal_object((PyObject*)&PyType_Type, ctx);
}

LEAN_EXPORT lean_obj_res nerodia_py_context_str_type(b_lean_obj_arg ctx) {
  return nerodia_of_immortal_object((PyObject*)&PyUnicode_Type, ctx);
}

/* ### Type Objects */

/** getQualName : @& PyType -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_py_type_get_qual_name(b_lean_obj_arg self) {
  return (size_t)PyType_GetQualName(nerodia_to_type_object(self));
}

LEAN_EXPORT uint8_t nerodia_py_type_is_heap_type(b_lean_obj_arg self) {
  return PyType_HasFeature(nerodia_to_type_object(self), Py_TPFLAGS_HEAPTYPE) != 0;
}

LEAN_EXPORT uint8_t nerodia_py_type_is_immutable(b_lean_obj_arg self) {
  return PyType_HasFeature(nerodia_to_type_object(self), Py_TPFLAGS_IMMUTABLETYPE) != 0;
}

/** ### Strings */

/* mkPyStr : @& String -> BaseIO (CPtr PyStr) */
LEAN_EXPORT size_t nerodia_mk_py_str(b_lean_obj_arg s) {
  // Lean strings include a null-terminator.
  // `FromStringAndSize` does not expect one, so use `size-1`.
  // Lean guarantees that the string is properly UTF-8 encoded.
  return (size_t)PyUnicode_FromStringAndSize(
    lean_string_cstr(s), lean_string_size(s)-1);
}

/* str : @& PyObject -> BaseIO (CPtr PyStr) */
LEAN_EXPORT size_t nerodia_py_object_str(b_lean_obj_arg o) {
  return (size_t)PyObject_Str(nerodia_to_object(o));
}

/* repr : @& PyObject -> BaseIO (CPtr PyStr) */
LEAN_EXPORT size_t nerodia_py_object_repr(b_lean_obj_arg o) {
  return (size_t)PyObject_Repr(nerodia_to_object(o));
}

/* toString : @& PyStr -> String */
LEAN_EXPORT lean_obj_res nerodia_py_str_to_string(b_lean_obj_arg o) {
  Py_ssize_t size;
  const char * cs = PyUnicode_AsUTF8AndSize(nerodia_to_object(o), &size);
  if (LEAN_LIKELY(cs != NULL)) {
    // Both Lean and `AsUTF8AndSize` have a null terminator,
    // but neither include it in `size`
    return lean_mk_string_from_bytes_unchecked(cs, size);
  }
  // It should be impossible for the encode to fail
  // except in the case of memory errors
  nerodia_exception_panic();
}

/* utf8Encode : @& PyStr -> BaseIO (CPtr PyBytes) */
LEAN_EXPORT size_t nerodia_py_str_utf8_encode(b_lean_obj_arg o) {
  return (size_t)PyUnicode_AsUTF8String(nerodia_to_object(o));
}

/* toByteArray : @& PyBytes -> ByteArray */
LEAN_EXPORT lean_obj_res nerodia_py_bytes_to_byte_array(b_lean_obj_arg self) {
  PyObject* o = nerodia_to_object(self);
  size_t sz = PyBytes_Size(o);
  lean_object* r = lean_alloc_sarray(1, sz, sz);
  memcpy(lean_sarray_cptr(r), PyBytes_AsString(o), sz);
  return r;
}
