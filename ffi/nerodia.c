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
static pthread_mutex_t g_py_mutex;
static pthread_once_t g_py_mutex_once = PTHREAD_ONCE_INIT;
static void py_init_mutex(void) {
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&g_py_mutex, &attr);
  pthread_mutexattr_destroy(&attr);
}
#define py_mutex_lock()   (pthread_once(&g_py_mutex_once, py_init_mutex), \
                           pthread_mutex_lock(&g_py_mutex))
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
  bool is_finalizing;
} py_environment;

static py_environment g_py_env = {
  .is_finalizing = false,
  .is_held = false,
  .holders = 0,
};

typedef struct {
  int holders;
  PyGILState_STATE gil;
} py_thread_ctx;

static _Thread_local py_thread_ctx g_py_ctx = {
  .holders = 0,
};

static lean_external_class* g_py_environment_external_class = NULL;
static lean_external_class* g_py_thread_ctx_external_class = NULL;
static lean_external_class* g_py_object_external_class = NULL;

static inline void py_ctx_init(void) {
  g_py_ctx.gil = PyGILState_Ensure();
}

// Increments the context reference counter.
// Returns whether the context is new and should be initialized.
static inline bool py_ctx_acquire(void) {
  return ++g_py_ctx.holders == 1;
}

// Must be paired with `py_gil_release`.
// Never increments the environment reference counter.
static inline void py_gil_ensure(void) {
  if (py_ctx_acquire()) py_ctx_init();
}

// Must be paired with `py_gil_ensure`.
// Never decrements the environment reference counter.
static inline void py_gil_release(void) {
  if (--g_py_ctx.holders == 0) {
    PyGILState_Release(g_py_ctx.gil);
  }
}

static inline void py_finalize(void) {
  if (g_py_env.is_finalizing) {
    // mutex is already locked and the GIL is still held by the finalizer
    return;
  }
  py_mutex_lock();
  if (!g_py_env.is_held) {
    // somebody else resurrected and finalized the environment first
    py_mutex_unlock();
    return;
  }
  // `g_py_env.holders > 0` implies we raced with the environment initializer,
  // they acquired the lock first, and they want the environment alive.
  if (atomic_load(&g_py_env.holders) == 0) {
    if (g_py_env.is_initializer) {
      // Must take GIL within the mutex to avoid deadlock with the mutex.
      // No environment holders implies no context holders / Nerodia GIL holders.
      g_py_ctx.holders = 1;
      py_ctx_init();
      // `Py_Finalize` may reenter Nerodia
      g_py_env.is_finalizing = true;
      Py_Finalize();
      g_py_ctx.holders = 0;
      g_py_env.is_finalizing = false;
      g_py_env.is_held = false;
      py_mutex_unlock();
      return;
    }
    g_py_env.is_held = false;
  }
  py_mutex_unlock();
}

static void py_environment_finalize(void* p) {
  if (atomic_fetch_sub(&g_py_env.holders, 1) == 1) {
    py_finalize();
  }
}

static void py_thread_ctx_foreach(void* p, b_lean_obj_arg f) {
  lean_internal_panic(
    "`PyThreadCtx` marked persistent or multi-threaded. "
    "This is forbidden as `PyThreadCtx` holds the Python GIL.");
}

static void py_thread_ctx_finalize(void* p) {
  if (--g_py_ctx.holders == 0) {
    PyGILState_Release(g_py_ctx.gil);
    if (atomic_fetch_sub(&g_py_env.holders, 1) == 1) {
      py_finalize();
    }
  }
}

static void py_object_finalize(void* p) {
  py_gil_ensure();
  Py_DECREF(p);
  py_gil_release();
  if (atomic_fetch_sub(&g_py_env.holders, 1) == 1) {
    py_finalize();
  }
}

static void py_env_ensure(void) {
  py_mutex_lock();
  if (g_py_env.is_held) {
    atomic_fetch_add(&g_py_env.holders, 1);
  } else {
    if (!g_py_environment_external_class) {
      g_py_environment_external_class = lean_register_external_class(
        py_environment_finalize, nop_foreach);
    }
    if (!g_py_thread_ctx_external_class) {
      g_py_thread_ctx_external_class = lean_register_external_class(
        py_thread_ctx_finalize, py_thread_ctx_foreach);
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
  }
  py_mutex_unlock();
}

/* getOrInit : BaseIO PyEnvironment */
LEAN_EXPORT lean_obj_res nerodia_py_environment_get_or_init(void) {
  py_env_ensure();
  return lean_alloc_external(g_py_environment_external_class, NULL);
}

/* getOrInit : BaseIO PyThreadCtx */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_get_or_init(void) {
  if (py_ctx_acquire()) {
    py_env_ensure();
    py_ctx_init();
  }
  return lean_alloc_external(g_py_thread_ctx_external_class, NULL);
}

/* mk : @& PyEnvironment -> BaseIO PyThreadCtx */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_mk(b_lean_obj_arg env) {
  if (py_ctx_acquire()) {
    atomic_fetch_add(&g_py_env.holders, 1);
    py_ctx_init();
  }
  return lean_alloc_external(g_py_thread_ctx_external_class, NULL);
}

/* env : @& PyThreadCtx -> PyEnvironment */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_env(b_lean_obj_arg ctx) {
  atomic_fetch_add(&g_py_env.holders, 1);
  // Remark: Consider caching this object if performance becomes an issue.
  return lean_alloc_external(g_py_environment_external_class, NULL);
}

static inline lean_obj_res nerodia_of_object(PyObject* o, b_lean_obj_arg env_or_ctx) {
  // convert reference to `env_or_ctx` to a global reference to the Python environment
  atomic_fetch_add(&g_py_env.holders, 1);
  return lean_alloc_external(g_py_object_external_class, o);
}

static inline lean_obj_res nerodia_of_immortal_object(PyObject* o, b_lean_obj_arg env_or_ctx) {
  // Note: Python 3.13+ allows references to immortal objects (e.g., types)
  // to be decremented without an increment, so we can avoid one here.
  return nerodia_of_object(o, env_or_ctx);
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
#define lean_mutex_lock() (InitOnceExecuteOnce(&g_lean_mutex_once, lean_init_mutex, NULL, NULL), \
                           EnterCriticalSection(&g_lean_mutex))
#define lean_mutex_unlock() LeaveCriticalSection(&g_lean_mutex)
#else
static pthread_mutex_t g_lean_mutex;
static pthread_once_t g_lean_mutex_once = PTHREAD_ONCE_INIT;
static void lean_init_mutex(void) {
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&g_lean_mutex, &attr);
  pthread_mutexattr_destroy(&attr);
}
#define lean_mutex_lock() (pthread_once(&g_lean_mutex_once, lean_init_mutex), \
                           pthread_mutex_lock(&g_lean_mutex))
#define lean_mutex_unlock() pthread_mutex_unlock(&g_lean_mutex)
#endif

void lean_initialize(void);
uint8_t lean_io_initializing(void);
uint8_t l_Lean_initializing(void);
lean_obj_res lean_set_initializing(uint8_t init);

static const char* g_mod_initializing = NULL;

/** Initializes Nerodia for use in a Python extension.  */
LEAN_EXPORT bool nerodia_initialize_lean(const char *mod_name) {
  // Remark: This function may be called from multiple Lean extension imports,
  // or if Lean code imports a Python module which imports Lean code, so it must
  // be idempotent and race-free in all cases.
  lean_mutex_lock();
  // TODO: Distinguish module initialization initiated by the Lean runtime from
  // initialization of the Lean runtime itself (likely requires a core change).
  if (lean_io_initializing()) {
    // Remark: Consider use of `lean_setup_args` via `Py_GetArgcArgv`.
    // However, it is not clear whether there is a good way to keep them in sync.
    lean_initialize();
    lean_init_task_manager();
    lean_io_mark_end_initialization();
  } else if (g_mod_initializing) {
    PyErr_Format(PyExc_ImportError, // TODO: Error class for Lean errors
      "Cannot initialize Lean module '%s' via Python during "
      "the initialization of '%s'. Recursive initialization is not supported.",
      mod_name, g_mod_initializing);
    lean_mutex_unlock();
    return false;
  } else if (l_Lean_initializing()) {
    PyErr_Format(PyExc_ImportError,
      "Cannot initialize Lean module '%s' via Python during "
      "Lean initialization. Recursive initialization is not supported.",
      mod_name);
    lean_mutex_unlock();
    return false;
  }
  g_mod_initializing = mod_name;
  lean_set_initializing(true);
  return true;
}

lean_obj_res lean_io_error_to_string(lean_obj_arg e);

/**
Marks the end of Nerodia initialization from Python.

`init_res` is result of the Lean module initialization.
*/
LEAN_EXPORT bool nerodia_mark_end_initialization(lean_obj_arg init_res) {
  assert(g_mod_initializing);
  bool ok = lean_io_result_is_ok(init_res);
  if (!ok) {
    lean_object* err = lean_io_result_get_error(init_res);
    lean_inc_ref(err);
    err = lean_io_error_to_string(err);
    PyErr_Format(PyExc_ImportError, // TODO: Error class for Lean errors
      "Failed to initialize Lean module '%s': %s",
      g_mod_initializing, lean_string_cstr(err));
    lean_dec_ref(err);
  }
  lean_dec_ref(init_res);
  g_mod_initializing = NULL;
  // Remark: Must hold mutex until here to avoid races on the `Lean.initializing` flag.
  lean_set_initializing(false);
  lean_mutex_unlock();
  return ok;
}

/* ## Lean API */

/* addr : @& PyObject -> Addr */
LEAN_EXPORT size_t nerodia_py_object_addr(b_lean_obj_arg self) {
  return (size_t)nerodia_to_object(self);
}

/* newRef : @& Py T -> CPyBaseIO (Py T) */
LEAN_EXPORT size_t nerodia_py_object_new_ref(b_lean_obj_arg self) {
  return (size_t)Py_NewRef(nerodia_to_object(self));
}

/* mkObjectUnsafe : @& PyEnvironment|PyThreadCtx -> CPyBaseResult α -> α */
LEAN_EXPORT lean_obj_res nerodia_mk_object(b_lean_obj_arg env_or_ctx, size_t ptr) {
  return nerodia_of_object((PyObject*)ptr, env_or_ctx);
}

/* mkArgUnsafe : @& PyThreadCtx ->  CPyArg α -> α */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_mk_arg(b_lean_obj_arg ctx, size_t ptr) {
  return nerodia_of_object(Py_NewRef((PyObject*)ptr), ctx);
}

/* mkArgsUnsafe : @& PyThreadCtx -> CPyArgs -> USize -> Array PyObject */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_mk_args(b_lean_obj_arg ctx, size_t args, size_t nargs) {
  lean_obj_res objs = lean_alloc_array(nargs, nargs);
  for (size_t i = 0; i < nargs; ++i) {
    lean_array_set_core(objs, i,
      nerodia_of_object(Py_NewRef(((PyObject**)args)[i]), ctx));
  }
  return objs;
}

/* mkNthArgUnsafe : @& PyThreadCtx -> CPyArgs -> USize -> PyObject */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_mk_nth_arg(b_lean_obj_arg ctx, size_t args, size_t i) {
  return nerodia_of_object(Py_NewRef(((PyObject**)args)[i]), ctx);
}

/* ### Exceptions */

/* clearError : @& PyThreadCtx -> BaseIO Unit */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_clear_error(b_lean_obj_arg ctx) {
  PyErr_Clear();
  return lean_box(0);
}

/* getCRaisedException : CPyIO PyBaseException */
LEAN_EXPORT size_t nerodia_get_raised_exception(void) {
  return (size_t)PyErr_GetRaisedException();
}

/* setRaisedExceptionUnsafe : @& PyBaseException -> BaseIO Unit */
LEAN_EXPORT lean_obj_res nerodia_set_raised_exception(b_lean_obj_arg e) {
  PyErr_SetRaisedException((PyObject*)Py_NewRef(nerodia_to_object(e)));
  return lean_box(0);
}

/* setExceptionResultUnsafe : CPyBaseResult PyBaseException -> BaseIO Unit */
LEAN_EXPORT lean_obj_res nerodia_set_exception_result(size_t e) {
  PyErr_SetRaisedException((PyObject*)e);
  return lean_box(0);
}

/* mkPyEOFError : CPyIO PyEOFError */
LEAN_EXPORT size_t nerodia_mk_py_eof_error() {
  return (size_t)PyObject_CallNoArgs(PyExc_EOFError);
}

static inline PyObject* mk_str(b_lean_obj_arg s) {
  // Lean strings include a null-terminator.
  // `FromStringAndSize` does not expect one, so use `size-1`.
  // Lean guarantees that the string is properly UTF-8 encoded.
  return PyUnicode_FromStringAndSize(
    lean_string_cstr(s), lean_string_size(s)-1);
}

static inline size_t calls(PyObject* err, b_lean_obj_arg msg) {
  PyObject* msg_obj = mk_str(msg);
  if (msg_obj == NULL) {
    return (size_t)NULL;
  }
  PyObject* ex = PyObject_CallFunctionObjArgs(
    err, msg_obj, NULL);
  Py_DECREF(msg_obj);
  return (size_t)ex;
}

/* mkPyTypeError : @& String -> CPyIO PyTypeError */
LEAN_EXPORT size_t nerodia_mk_py_type_error(b_lean_obj_arg msg) {
  return calls(PyExc_TypeError, msg);
}

/* mkPyValueError : @& String -> CPyIO PyValueError */
LEAN_EXPORT size_t nerodia_mk_py_value_error(b_lean_obj_arg msg) {
  return calls(PyExc_ValueError, msg);
}

/* mkPyRuntimeError : @& String -> CPyIO PyRuntimeError */
LEAN_EXPORT size_t nerodia_mk_py_runtime_error(b_lean_obj_arg msg) {
  return calls(PyExc_RuntimeError, msg);
}

/* mkPyOSError2 : UInt32 -> @& String -> CPyIO PyOSError */
LEAN_EXPORT size_t nerodia_mk_py_os_error2(
  uint32_t errno_l, b_lean_obj_arg strerror_l
) {
  PyObject* errno_obj = PyLong_FromUInt32(errno_l);
  if (errno_obj == NULL) {
    return (size_t)NULL;
  }
  PyObject* strerror_obj = mk_str(strerror_l);
  if (strerror_obj == NULL) {
    Py_DECREF(errno_obj);
    return (size_t)NULL;
  }
  PyObject* ex = PyObject_CallFunctionObjArgs(
    PyExc_OSError, errno_obj, strerror_obj, NULL);
  Py_DECREF(errno_obj);
  Py_DECREF(strerror_obj);
  return (size_t)ex;
}

/* mkPyOSError3 : UInt32 -> @& String -> @& System.FilePath -> CPyIO PyOSError */
LEAN_EXPORT size_t nerodia_mk_py_os_error3(
  uint32_t errno_l, b_lean_obj_arg strerror_l, b_lean_obj_arg filename
) {
  PyObject* errno_obj = PyLong_FromUInt32(errno_l);
  if (errno_obj == NULL) {
    return (size_t)NULL;
  }
  PyObject* strerror_obj = mk_str(strerror_l);
  if (strerror_obj == NULL) {
    Py_DECREF(errno_obj);
    return (size_t)NULL;
  }
  PyObject* filename_obj = mk_str(filename);
  if (filename_obj == NULL) {
    Py_DECREF(errno_obj);
    Py_DECREF(strerror_obj);
    return (size_t)NULL;
  }
  PyObject* ex = PyObject_CallFunctionObjArgs(
    PyExc_OSError, errno_obj, strerror_obj, filename_obj, NULL);
  Py_DECREF(errno_obj);
  Py_DECREF(strerror_obj);
  Py_DECREF(filename_obj);
  return (size_t)ex;
}

LEAN_NORETURN void nerodia_exception_panic(void) {
  if (PyErr_ExceptionMatches(PyExc_MemoryError)) {
    lean_internal_panic_out_of_memory();
  } else {
    PyErr_WriteUnraisable(NULL);
    lean_internal_panic_unreachable();
  }
}

/* systemError : @& String -> @& PyThreadCtx -> PySystemError */
LEAN_EXPORT lean_obj_res nerodia_py_thread_ctx_system_error(b_lean_obj_arg msg, b_lean_obj_arg ctx) {
  py_gil_ensure();
  PyObject* msg_obj = mk_str(msg);
  if (LEAN_LIKELY(msg_obj != NULL)) {
    PyObject* ex = PyObject_CallFunctionObjArgs(
      PyExc_SystemError, msg_obj, NULL);
    Py_DECREF(msg_obj);
    if (LEAN_LIKELY(ex != NULL)) {
      py_gil_release();
      return nerodia_of_object(ex, ctx);
    }
  }
  nerodia_exception_panic();
}

/* ### Etc */

/* none : @& PyEnvironment -> PyNone */
LEAN_EXPORT lean_obj_res nerodia_py_environment_none(b_lean_obj_arg env) {
  return nerodia_of_immortal_object(Py_None, env);
}

/* getPyNone : CPyBaseIO PyNone */
LEAN_EXPORT size_t nerodia_get_py_none() {
  return (size_t)Py_None;
}

/* isNone : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_none(b_lean_obj_arg self) {
  return nerodia_to_object(self) == Py_None;
}

/* import : @& String -> CPyIO PyObject */
LEAN_EXPORT size_t nerodia_import(b_lean_obj_arg mod_name) {
  return (size_t)PyImport_ImportModule(lean_string_cstr(mod_name));
}

/* addByString : @& String -> @& PyObject -> @& Module -> CPyUnitIO */
LEAN_EXPORT uint32_t nerodia_py_module_add_by_string
  (b_lean_obj_arg name, b_lean_obj_arg val, b_lean_obj_arg mod)
{
  return PyModule_AddObjectRef(nerodia_to_object(mod),
    lean_string_cstr(name), nerodia_to_object(val));
}

/* getAttrByString : @& PyObject -> @& String -> CPyIO PyObject */
LEAN_EXPORT size_t nerodia_py_object_get_attr_by_string(b_lean_obj_arg self, b_lean_obj_arg attr_name) {
  return (size_t)PyObject_GetAttrString(nerodia_to_object(self), lean_string_cstr(attr_name));
}

/* ### Types */

/** getType : @& PyObject -> CPyBaseIO PyType  */
LEAN_EXPORT size_t nerodia_py_object_get_type(b_lean_obj_arg self) {
  return (size_t)Py_NewRef((PyObject*)Py_TYPE(nerodia_to_object(self)));
}

/* isTypeInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_type_instance(b_lean_obj_arg self) {
  return PyType_Check(nerodia_to_object(self));
}

/* isBaseExceptionInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_base_exception_instance(b_lean_obj_arg self) {
  return PyExceptionInstance_Check(nerodia_to_object(self));
}

/* isStrInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_str_instance(b_lean_obj_arg self) {
  return PyUnicode_Check(nerodia_to_object(self));
}

/* isBytesInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_bytes_instance(b_lean_obj_arg self) {
  return PyBytes_Check(nerodia_to_object(self));
}

/* isIntInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_int_instance(b_lean_obj_arg self) {
  return PyLong_Check(nerodia_to_object(self));
}

/* isModuleInstance : @& PyObject -> Bool */
LEAN_EXPORT uint8_t nerodia_py_object_is_module_instance(b_lean_obj_arg self) {
  return PyModule_Check(nerodia_to_object(self));
}

/* ### Types */

/** getQualName : @& PyType -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_py_type_get_qual_name(b_lean_obj_arg self) {
  return (size_t)PyType_GetQualName(nerodia_to_type_object(self));
}

/** ### Strings */

/* mkPyStr : @& String -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_mk_py_str(b_lean_obj_arg s) {
  return (size_t)mk_str(s);
}

/* str : @& PyObject -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_py_object_str(b_lean_obj_arg o) {
  return (size_t)PyObject_Str(nerodia_to_object(o));
}

/* repr : @& PyObject -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_py_object_repr(b_lean_obj_arg o) {
  return (size_t)PyObject_Repr(nerodia_to_object(o));
}

/* toString : @& PyStr -> String */
LEAN_EXPORT lean_obj_res nerodia_py_str_to_string(b_lean_obj_arg self) {
  py_gil_ensure();
  Py_ssize_t size;
  PyObject * o = nerodia_to_object(self);
  const char * cs = PyUnicode_AsUTF8AndSize(o, &size);
  if (LEAN_LIKELY(cs != NULL)) {
    py_gil_release();
    // Both Lean and `AsUTF8AndSize` have a null terminator,
    // but neither include it in `size`
    return lean_mk_string_from_bytes_unchecked(cs, size);
  } else if (PyErr_ExceptionMatches(PyExc_UnicodeEncodeError)) {
    PyErr_Clear();
    PyObject* b = PyUnicode_AsEncodedString(o, "utf-8", "surrogatepass");
    if (LEAN_LIKELY(b != NULL)) {
      lean_obj_res r = lean_mk_string_from_bytes(
        PyBytes_AsString(b), PyBytes_Size(b));
      Py_DECREF(b);
      py_gil_release();
      return r;
    }
  }
  // It should be impossible for the encode to fail
  // except in the case of memory errors
  nerodia_exception_panic();
}

/* encode : @& PyStr -> @& String -> @& String -> CPyIO PyBytes */
LEAN_EXPORT size_t nerodia_py_str_encode(
  b_lean_obj_arg self, b_lean_obj_arg encoding, b_lean_obj_arg errors
) {
  return (size_t)PyUnicode_AsEncodedString(nerodia_to_object(self),
    lean_string_cstr(encoding), lean_string_cstr(errors));
}

/* utf8Encode : @& PyStr -> CPyIO PyBytes */
LEAN_EXPORT size_t nerodia_py_str_encode_utf8(b_lean_obj_arg o) {
  return (size_t)PyUnicode_AsUTF8String(nerodia_to_object(o));
}

/* decode : @& ByteArray -> @& String -> @& String -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_decode(
  b_lean_obj_arg bytes, b_lean_obj_arg encoding, b_lean_obj_arg errors
) {
  return (size_t)PyUnicode_Decode(
    (const char *)lean_sarray_cptr(bytes), lean_sarray_size(bytes),
    lean_string_cstr(encoding), lean_string_cstr(errors));
}

/* decode : @& PyBuffer -> @& String -> @& String -> CPyIO PyStr */
LEAN_EXPORT size_t nerodia_py_buffer_decode(
  b_lean_obj_arg self, b_lean_obj_arg encoding, b_lean_obj_arg errors
) {
  return (size_t)PyUnicode_FromEncodedObject(nerodia_to_object(self),
    lean_string_cstr(encoding), lean_string_cstr(errors));
}

/** ### Bytes */

/* bytes : @& PyObject -> CPyIO PyBytes */
LEAN_EXPORT size_t nerodia_py_object_bytes(b_lean_obj_arg o) {
  return (size_t)PyObject_Bytes(nerodia_to_object(o));
}

/* mkPyBytes : @& ByteArray -> CPyIO PyBytes */
LEAN_EXPORT size_t nerodia_mk_py_bytes(b_lean_obj_arg self) {
  return (size_t)PyBytes_FromStringAndSize(
    (const char *)lean_sarray_cptr(self), lean_sarray_size(self));
}

/* usize : @& PyBytes -> USize */
LEAN_EXPORT size_t nerodia_py_bytes_usize(b_lean_obj_arg self) {
  // Note: Context not needed as operations are immutable pointer accesses
  PyObject* o = nerodia_to_object(self);
  // `self` must be a proper Python bytes object to avoid raising an error.
  assert(PyBytes_Check(o));
  return PyBytes_Size(o);
}

/* toByteArray : @& PyBytes -> ByteArray */
LEAN_EXPORT lean_obj_res nerodia_py_bytes_to_byte_array(b_lean_obj_arg self) {
  // Note: Context not needed as operations are immutable pointer accesses.
  PyObject* o = nerodia_to_object(self);
  // `self` must be a proper Python bytes object to avoid raising an error.
  assert(PyBytes_Check(o));
  Py_ssize_t sz = PyBytes_Size(o);
  lean_object* r = lean_alloc_sarray(1, sz, sz);
  memcpy(lean_sarray_cptr(r), PyBytes_AsString(o), sz);
  return r;
}

/* checkBufferUnsafe : @& PyObject -> BaseIO Bool */
LEAN_EXPORT uint8_t nerodia_py_object_check_buffer(b_lean_obj_arg o) {
  return PyObject_CheckBuffer(nerodia_to_object(o));
}

/* getByteArrayUnsafe : @& PyBuffer -> BaseIO (Option ByteArray) */
LEAN_EXPORT lean_obj_res nerodia_py_buffer_get_byte_array(b_lean_obj_arg buf) {
  // When Nerodia supports free-threading, ensure thread-safe buffer use.
  Py_buffer view;
  PyObject *buf_obj = nerodia_to_object(buf);
  if (PyObject_GetBuffer(buf_obj, &view, PyBUF_SIMPLE) < 0) {
    return lean_box(0); // Option.none
  }
  lean_object* ba = lean_alloc_sarray(1, view.len, view.len);
  memcpy(lean_sarray_cptr(ba), view.buf, view.len);
  PyBuffer_Release(&view);
  lean_object* opt = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(opt, 0, ba); // Option.some
  return opt;
}

/** ### Integers */

/* int : @& PyObject -> CPyIO PyInt */
LEAN_EXPORT size_t nerodia_py_object_int(b_lean_obj_arg o) {
  return (size_t)PyNumber_Long(nerodia_to_object(o));
}

/* index : @& PyObject -> CPyIO PyInt */
LEAN_EXPORT size_t nerodia_py_object_index(b_lean_obj_arg o) {
  return (size_t)PyNumber_Index(nerodia_to_object(o));
}

/* mkPyIntLE : @& ByteArray -> CPyIO PyInt */
LEAN_EXPORT size_t nerodia_mk_py_int_le(b_lean_obj_arg bs) {
  return (size_t)PyLong_FromNativeBytes(
      (const char *)lean_sarray_cptr(bs),
      lean_sarray_size(bs), Py_ASNATIVEBYTES_LITTLE_ENDIAN);
}

size_t nerodia_mk_big_py_int(lean_obj_arg n);

/* mkPyInt : Int -> CPyIO PyInt */
LEAN_EXPORT size_t nerodia_mk_py_int(b_lean_obj_arg n) {
  if (lean_is_scalar(n)) {
    return (size_t)PyLong_FromInt64(lean_scalar_to_int64(n));
  } else {
    lean_inc_ref(n);
    return nerodia_mk_big_py_int(n);
  }
}

/* mkPyNat : Nat -> CPyIO PyInt */
LEAN_EXPORT size_t nerodia_mk_py_nat(b_lean_obj_arg n) {
  if (lean_is_scalar(n)) {
    return (size_t)PyLong_FromSize_t(lean_unbox(n));
  } else {
    lean_inc_ref(n);
    return nerodia_mk_big_py_int(n);
  }
}

static inline lean_obj_res py_int_to_byte_array(b_lean_obj_arg self, int flags) {
  // Note: `PyLong_AsNativeBytes` is only called with arguments that cannot
  // error, and a Python `int` is immutable, so we do not need a context here.
  PyObject *v = nerodia_to_object(self);
  assert(PyLong_Check(v));
  Py_ssize_t n_bytes = PyLong_AsNativeBytes(v, NULL, 0, flags);
  assert(n_bytes != -1);
  lean_object* r = lean_alloc_sarray(1, n_bytes, n_bytes);
  n_bytes = PyLong_AsNativeBytes(v, lean_sarray_cptr(r), n_bytes, flags);
  assert(n_bytes != -1);
  return r;
}

/* toByteArrayLE : @& PyInt -> ByteArray */
LEAN_EXPORT lean_obj_res nerodia_py_int_to_byte_array_le(b_lean_obj_arg self) {
  return py_int_to_byte_array(self, Py_ASNATIVEBYTES_LITTLE_ENDIAN);
}

/* toByteArrayBE : @& PyInt -> ByteArray */
LEAN_EXPORT lean_obj_res nerodia_py_int_to_byte_array_be(b_lean_obj_arg self) {
  return py_int_to_byte_array(self, Py_ASNATIVEBYTES_BIG_ENDIAN);
}
