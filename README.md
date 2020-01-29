# Verifying concurrent, crash-safe systems

[![Build Status](https://travis-ci.org/mit-pdos/perennial.svg?branch=master)](https://travis-ci.org/mit-pdos/perennial)

Verifying refinement for systems with both concurrency and crash-safety requirements, including recovery procedures. For example, think of file systems, concurrent write-ahead logging like Linux's jbd2 layer, and persistent key-value stores like RocksDB.

Perennial uses [Goose](https://github.com/tchajed/goose) to enable verification of programs written in (a subset of) Go.

## Compiling

We develop Perennial using Coq master and maintain compatibility with Coq 8.11.

This project uses git submodules to include several dependencies. You can either use `git clone --recurse-submodules` or (after cloning) `git submodule update --init --recursive` to set that up.

We compile with [coqc.py](etc/coqc.py), a Python wrapper around `coqc` to get timing information; due to limitations in the Makefile, this wrapper is required to pass the right flags to Coq even if not using the timing information. You'll need Python3 and the `argparse` library (`pip3 install argparse`) to run the wrapper.

To compile just run `make` with Coq on your `$PATH`.

## Publications

Perennial is described in our SOSP paper, "[Verifying concurrent, crash-safe systems with Perennial](https://www.chajed.io/papers/perennial:sosp2019.pdf)".

Goose is briefly described in a CoqPL extended abstract and associated talk, "[Verifying concurrent Go code in Coq with Goose](https://www.chajed.io/papers/goose:coqpl2020.pdf)".
