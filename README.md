# Verifying concurrent, crash-safe systems

[![Build Status](https://travis-ci.org/mit-pdos/perennial.svg?branch=master)](https://travis-ci.org/mit-pdos/perennial)

Verifying refinement for systems with both concurrency and crash-safety requirements, including recovery procedures. For example, think of file systems, concurrent write-ahead logging like Linux's jbd2 layer, and persistent key-value stores like RocksDB.

The two big verified examples we have so far are Mailboat, a Go mail server, and a replicated disk (which doesn't connect to Go but is executable using Haskell extraction).

## Compiling

We develop Perennial using Coq master. We also maintain compatibility with Coq v8.9.1, which is tested as part of continuous integration.

This project uses git submodules to include several dependencies. You can either use `git clone --recurse-submodules` or (after cloning) `git submodule update --init --recursive` to set that up.

We compile with [coqc.py](etc/coqc.py), a Python wrapper around `coqc` to get timing information; due to limitations in the Makefile, this wrapper is required to pass the right flags to Coq even if not using the timing information. You'll need Python3 and the `argparse` library (`pip3 install argparse`) to run the wrapper.

To compile just run `make` with Coq on your `$PATH`.

## Verifying systems written in Go

We reason about Go code by importing it into a model in Coq that Perennial supports, using a tool called Goose available at <https://github.com/tchajed/goose>. To be self-contained this repository has a committed version of the `goose`-generated Coq model for Mailboat, whose implementation is at <https://github.com/tchajed/mailboat>.

## Publications

Perennial is described in an upcoming SOSP paper, "[Verifying concurrent, crash-safe systems with Perennial](https://www.chajed.io/papers/perennial:sosp2019.pdf)".
