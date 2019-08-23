# Verifying concurrent and crash-safe systems

[![Build Status](https://travis-ci.org/mit-pdos/armada.svg?branch=master)](https://travis-ci.org/mit-pdos/armada)

Verifying refinement for systems with both concurrency and crash-safety requirements, including recovery procedures. For example, think of file systems, concurrent write-ahead logging like Linux's jbd2 layer, and persistent key-value stores like RocksDB.

## Compiling

We develop Armada using Coq master. We also maintain compatibility with Coq v8.9.1, which is tested as part of continuous integration.

This project uses git submodules to include several dependencies. You can either use `git clone --recurse-submodules` or (after cloning) `git submodule update --init --recursive` to set that up.

We compile with [coqc.py](etc/coqc.py), a Python wrapper around `coqc` to get timing information; due to limitations in the Makefile, this wrapper is required to pass the right flags to Coq even if not using the timing information. You'll need Python3 and the `argparse` library (`pip3 install argparse`) to run the wrapper.

To compile just run `make` with Coq on your `$PATH`.
