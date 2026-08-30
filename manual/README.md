# Nerodia Reference Manual

A reference manual for Nerodia, written in Verso.

To build it, ensure Python's shared libraries are in the shared library path and run:

```
$ lake exe docs
```

The generated site will be in `_out/html-multi/`. Serve it with:

```
$ lake exe verso-serve _out/html-multi
```
