/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
*/
#include <Python.h>
#include <lean/lean.h>
#include <string.h>

/* ## Basics */

static void nop_foreach(void* p, b_lean_obj_arg f) {
  return;
}

static lean_object * g_py_context = NULL;

typedef struct {
  bool is_main;
  bool is_initializer;
  PyGILState_STATE gil;
} py_context;

static void py_context_finalize(void* p) {
  // TODO: acquire a g_py initialization/finalization mutex
  py_context* pctx = (py_context*)p;
  if (pctx->is_initializer) {
    Py_Finalize();
  } else {
    PyGILState_Release(pctx->gil);
  }
  if (pctx->is_main) {
    g_py_context = NULL;
  } else {
    lean_dec_ref(g_py_context);
  }
  free(pctx);
}

static void py_object_finalize(void* p) {
  PyGILState_STATE gil = PyGILState_Ensure();
  Py_DECREF(p);
  PyGILState_Release(gil);
  lean_dec_ref(g_py_context);
}

static lean_external_class * g_py_context_external_class = NULL;
static lean_external_class * g_py_object_external_class = NULL;

LEAN_EXPORT lean_obj_res nerodia_py_context_get_or_init() {
  // TODO: acquire a g_py initialization/finalization mutex
  py_context * pctx = malloc(sizeof(py_context));
  if (g_py_context) {
    lean_inc_ref(g_py_context);
    pctx->is_main = false;
    pctx->is_initializer = false;
    pctx->gil = PyGILState_Ensure();
    return lean_alloc_external(g_py_context_external_class, pctx);
  } else {
    if (!g_py_context_external_class) {
      g_py_context_external_class = lean_register_external_class(
        py_context_finalize, nop_foreach);
    }
    if (!g_py_object_external_class) {
      g_py_object_external_class = lean_register_external_class(
        py_object_finalize, nop_foreach);
    }
    pctx->is_main = true;
    if (Py_IsInitialized()) {
      pctx->is_initializer = false;
      pctx->gil = PyGILState_Ensure();
    } else {
      Py_Initialize();
      pctx->is_initializer = true;
    }
    g_py_context = lean_alloc_external(g_py_context_external_class, pctx);
    return g_py_context;
  }
}

lean_obj_res nerodia_of_object_core(PyObject* o) {
  return lean_alloc_external(g_py_object_external_class, o);
}

static inline lean_obj_res nerodia_of_object(PyObject* o, lean_obj_arg ctx) {
  // Convert a reference to a potentially thread-local context
  // to a refernce to the global context. Objects can live outside there
  // threads and hold strong refernces to the main context.
  lean_inc_ref(g_py_context); lean_dec_ref(ctx);
  return nerodia_of_object_core(o);
}

static inline lean_obj_res nerodia_of_immortal_object(PyObject* o, lean_obj_arg ctx) {
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

/* ## API */

LEAN_EXPORT size_t nerodia_py_object_addr(b_lean_obj_arg self) {
  return (size_t)nerodia_to_object(self);
}

LEAN_EXPORT lean_obj_res nerodia_py_object_ctx(b_lean_obj_arg self) {
  // Since the Python object `self` exists, `g_py_context != NULL`
  lean_inc_ref(g_py_context);
  return g_py_context;
}

LEAN_EXPORT lean_obj_res nerodia_py_context_clear_error(b_lean_obj_arg ctx) {
  PyErr_Clear();
  return lean_box(0);
}

LEAN_EXPORT lean_obj_res nerodia_py_context_get_raised_exception(lean_obj_arg ctx) {
  PyObject *ex = PyErr_GetRaisedException();
  if (ex) {
    lean_obj_res r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, nerodia_of_object(ex, ctx));
    return r;
  } else {
    lean_dec_ref(ctx);
    return lean_box(0);
  }
}

LEAN_EXPORT lean_obj_res nerodia_py_context_none(lean_obj_arg ctx) {
  return nerodia_of_immortal_object(Py_None, ctx);
}

/* ### Types */

LEAN_EXPORT lean_obj_res nerodia_py_object_type(b_lean_obj_arg self) {
  lean_inc_ref(g_py_context); // `self` implies a main context we can grab
  // `PyObject_Type` cannot fail as Nerodia guarantees the pointer in `self` is non-NULL
  return nerodia_of_object_core(PyObject_Type(nerodia_to_object(self)));
}

LEAN_EXPORT uint8_t nerodia_py_object_is_type_instance(b_lean_obj_arg self) {
  return PyType_Check(nerodia_to_object(self)) != 0;
}

LEAN_EXPORT uint8_t nerodia_py_object_is_str_instance(b_lean_obj_arg self) {
  return PyUnicode_Check(nerodia_to_object(self)) != 0;
}

LEAN_EXPORT lean_obj_res nerodia_py_context_type_type(lean_obj_arg ctx) {
  return nerodia_of_immortal_object((PyObject*)&PyType_Type, ctx);
}

LEAN_EXPORT lean_obj_res nerodia_py_context_str_type(lean_obj_arg ctx) {
  return nerodia_of_immortal_object((PyObject*)&PyUnicode_Type, ctx);
}

/* ### Type Objects */

LEAN_EXPORT lean_obj_res nerodia_py_type_object_get_qual_name(b_lean_obj_arg self, lean_obj_arg ctx) {
  // TODO: handle potential errors here (allocation and static type name decode)
  return nerodia_of_object(PyType_GetQualName(nerodia_to_type_object(self)), ctx);
}

LEAN_EXPORT uint8_t nerodia_py_type_object_is_heap_type(b_lean_obj_arg self) {
  return PyType_HasFeature(nerodia_to_type_object(self), Py_TPFLAGS_HEAPTYPE) != 0;
}

LEAN_EXPORT uint8_t nerodia_py_type_object_is_immutable(b_lean_obj_arg self) {
  return PyType_HasFeature(nerodia_to_type_object(self), Py_TPFLAGS_IMMUTABLETYPE) != 0;
}

/** ### Strings */

LEAN_EXPORT lean_obj_res nerodia_mk_string(b_lean_obj_arg s, lean_obj_arg ctx) {
  // Lean strings include a null-terminator.
  // `FromStringAndSize` does not expect one, so use `size-1`.
  // Lean guarantees that the string is properly UTF-8 encoded.
  // TODO: handle potential allocation errors here
  PyObject * o = PyUnicode_FromStringAndSize(lean_string_cstr(s), lean_string_size(s)-1);
  return nerodia_of_object(o, ctx);
}

/* str : PyObject -> PyContext -> BaseIO (Option PyStrObject) */
LEAN_EXPORT lean_obj_res nerodia_py_object_str(b_lean_obj_arg o, lean_obj_arg ctx) {
  PyObject * s = PyObject_Str(nerodia_to_object(o));
  if (s) {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, nerodia_of_object(s, ctx));
    return r;
  } else {
    lean_dec_ref(ctx);
    return lean_box(0);
  }
}

/* repr : PyObject -> PyContext -> BaseIO (Option PyStrObject) */
LEAN_EXPORT lean_obj_res nerodia_py_object_repr(b_lean_obj_arg o, lean_obj_arg ctx) {
  PyObject * s = PyObject_Repr(nerodia_to_object(o));
  if (s) {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, nerodia_of_object(s, ctx));
    return r;
  } else {
    lean_dec_ref(ctx);
    return lean_box(0);
  }
}

/* getString : PyStrObject -> PyContext -> BaseIO (Option String) */
LEAN_EXPORT lean_obj_res nerodia_py_str_object_get_string(b_lean_obj_arg o, lean_obj_arg ctx) {
  Py_ssize_t size;
  const char * cs = PyUnicode_AsUTF8AndSize(nerodia_to_object(o), &size);
  if (LEAN_LIKELY(cs != NULL)) {
    // Both Lean and `AsUTF8AndSize` have a null terminator,
    // but neither include it in `size`
    lean_obj_res s = lean_mk_string_from_bytes_unchecked(cs, size);
    lean_dec_ref(ctx);
    lean_obj_res r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, s);
    return r;
  } else {
    lean_dec_ref(ctx);
    return lean_box(0);
  }
}

/* decoeUtf8 : PyStrObject -> PyContext -> BaseIO (Option PyBytesObjects) */
LEAN_EXPORT lean_obj_res nerodia_py_str_object_decode_utf8(b_lean_obj_arg o, lean_obj_arg ctx) {
  PyObject * bytes = PyUnicode_AsUTF8String(nerodia_to_object(o));
  if (bytes) {
    lean_obj_res v = nerodia_of_object(bytes, ctx);
    lean_obj_res r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
  } else {
    lean_dec_ref(ctx);
    return lean_box(0);
  }
}

LEAN_EXPORT lean_obj_res nerodia_py_bytes_object_to_byte_array(b_lean_obj_arg self) {
  PyObject* o = nerodia_to_object(self);
  size_t sz = PyBytes_Size(o);
  lean_object* r = lean_alloc_sarray(1, sz, sz);
  memcpy(lean_sarray_cptr(r), PyBytes_AsString(o), sz);
  return r;
}
