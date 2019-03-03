# Verifying concurrent and crash-safe systems

[![Build Status](https://travis-ci.org/mit-pdos/armada.svg?branch=master)](https://travis-ci.org/mit-pdos/armada)

Verifying refinement for systems with both concurrency and crash-safety requirements, including recovery procedures. For example, think of file systems, concurrent write-ahead logging like Linux's jbd2 layer, and persistent key-value stores like RocksDB.

## Compiling

We develop Armada using Coq master. It should be compatible with Coq v8.9.0, which is also tested as part of continuous integration.

This project uses git submodules to include several dependencies. You can either use `git clone --recurse-submodules` or (after cloning) `git submodule update --init --recursive` to set that up.

To compile just run `make` with Coq on your `$PATH`.
