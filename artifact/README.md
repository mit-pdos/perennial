---
title: "Verifying concurrent storage systems with Armada"
---

[![Build Status](https://travis-ci.org/mit-pdos/armada.svg?branch=master)](https://travis-ci.org/mit-pdos/armada)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

The code is licensed under the MIT license.

This artifact is licensed under the Creative Commons Attribution license.

# Getting started

## Installing dependencies

- Armada (requires Coq)
- Mailboat (requires Go)
- Goose (optional, requires Go): the output of Goose on Mailboat is committed to
  the Armada repo for convenience, but you can re-generate them exactly by
  running Goose.
- CMAIL (requires Coq and Haskell Stack)
- GoMail (requires Go)

Our code is open source; please feel free to share anything in this artifact or
the codebase (although please point people to GitHub rather than this static
artifact).

# About this artifact

This artifact was prepared by using `armada/artifact/prepare.sh`, which calls
`armada/release.sh` to package up the Argosy source code. The release consists
of copying the git repo and then deleting things.

The VM was produced by preparing the artifact, using the packer setup in
`armada/artifact/vm` to do an unattended install of Xubuntu, and finally manually
installing the artifact in the resulting VM and re-exporting it.
