# Recovery refinement

[![Build Status](https://travis-ci.org/mit-pdos/argosy.svg?branch=master)](https://travis-ci.org/mit-pdos/argosy)

Proving crash safety of systems by proving an implementation refines a specification. Supports implementations that run a recovery procedure, as well as abstracting away the behavior of the recovery procedure.

## Compiling

We develop Argosy using Coq master but remain compatible with Coq v8.9+beta and Coq v8.8.2 using continuous integration.

This project uses git submodules to include several dependencies. You can either use `git clone --recurse-submodules` or (after cloning) `git submodule --init --recursive` to set that up.

To compile just run `make` with Coq on your `$PATH`.
