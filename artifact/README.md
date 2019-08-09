---
title: "Verifying concurrent storage systems with Armada"
---

[![Build Status](https://travis-ci.org/mit-pdos/armada.svg?branch=master)](https://travis-ci.org/mit-pdos/armada)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

The code is licensed under the MIT license.

This artifact is licensed under the Creative Commons Attribution license.

# Getting started

The easiest way to use the artifact is to use the provided VirtualBox image. We
have one set of performance numbers that don't reproduce well in a VM, but this
is not the core of the paper's claims. It is also possible to run part of that
experiment using only Go.

## Code and dependencies

As a quick reference, here's the code the artifact covers:

- Armada, which includes mailboat as an example
- Goose
- Mailboat (a Go mail server, written in the Goose subset)

Here are the dependencies for the artifact (just for reference; all of these are
in the VM image):

- Haskell Stack
- Coq v8.9 or Coq master
- CSPEC
  - CMAIL (requires building with Coq and Haskell Stack)
  - GoMail
- gnuplot
- postal (a mail server benchmarking library)

Our code is open source; please feel free to share anything in this artifact or
the codebase (although please point people to GitHub rather than this static
artifact).

# About this artifact

The artifact documentation was prepared by using `armada/artifact/prepare.sh`.

The VM first does an unattended install of Xubuntu 19.04 using the packer setup
in `armada/artifact/vm`, then we installed all the dependencies (and several
conveniences such as a terminal and ZSH setup) manually.

Finally, we installed the code, which means:

- Clone the Armada and CSPEC repos into the home directory.
- Install the Go dependencies with `go get -u github.com/tchajed/mailboat/...`
  and `go get -u github.com/tchajed/goose/...`. Go clones the source code to
  `~/go/src/github.com/tchajed/` and also compiles and installs the binaries,
  `goose` and `mailboat-server`.
