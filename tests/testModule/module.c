/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
*/
#include <Python.h>
#include <lean/lean.h>

//void lean_initialize(); // if uses Lean.*
void lean_initialize_runtime_module(); // otherwise
//lean_object* lean_enable_initializer_execution(); // for custom initializers
lean_object* initialize_test_Test(uint8_t builtin);
size_t test_mk_greeting();

static int module_exec(PyObject *m) {
    lean_object* res;
    // TOOD: do not re-intialize on reimport
    lean_initialize_runtime_module();
    // res = lean_enable_initializer_execution(); // cannot actually fail
    // lean_dec_ref(res);
    // TODO: handle initialization function failures
    res = initialize_test_Test(true);
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    return 0;
}

static PyObject* mk_greeting(PyObject* self, PyObject* Py_UNUSED(args)) {
    return (PyObject*)test_mk_greeting();
}

static PyMethodDef module_methods[] = {
    {"mkGreeting", mk_greeting, METH_NOARGS, "Return a greeting."},
    {NULL, NULL, 0, NULL}
};

static PyModuleDef_Slot module_slots[] = {
    {Py_mod_exec, module_exec},
    {0, NULL}
};

static struct PyModuleDef module = {
    .m_base = PyModuleDef_HEAD_INIT,
    .m_name = "testmodule._native",
    .m_size = 0,
    .m_methods = module_methods,
    .m_slots = module_slots,
};

PyMODINIT_FUNC PyInit__native(void) {
    return PyModuleDef_Init(&module);
}
