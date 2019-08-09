---
title: "Verifying concurrent storage systems with Armada"
---

<table>
<tr>
<th>Armada</th>
<th>Goose</th>
<th>Mailboat</th>
<th>Artifact</th>
</tr>

<tr>
<td>
[![Build Status](https://travis-ci.org/mit-pdos/armada.svg?branch=master)](https://travis-ci.org/mit-pdos/armada)
</td>
<td>
[![Build Status](https://travis-ci.org/tchajed/goose.svg?branch=master)](https://travis-ci.org/tchajed/goose)
</td>
<td>
[![Build Status](https://travis-ci.com/tchajed/mailboat.svg?branch=master)](https://travis-ci.com/tchajed/mailboat)
</td>
<td>
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)
</td>
</tr>
</table>

The code is licensed under the MIT license.

This artifact is licensed under the Creative Commons Attribution license.

# Getting started

The easiest way to use the artifact is to use the provided VirtualBox image. We
have one set of performance numbers that don't reproduce well in a VM, but this
is not the core of the paper's claims. It is also possible to run part of that
experiment using only Go.

Here are some details on the virtual machine:

- The virtual machine appliance is around 3.5GB, and 12GB when extracted.
- The default login is `ubuntu` with no password.
- The default user has sudo access without a password.
- The VM has port forwarding from host port 11737 to SSH in the VM; all you need
  to do is `ssh -p 11737 ubuntu@localhost` to SSH to the virtual machine.
- The default user's shell is a slightly customized zsh.

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
- Python
- gnuplot
- postal (a mail server benchmarking library)

Our code is open source; please feel free to share anything in this artifact or
the codebase (although please point people to GitHub rather than this static
artifact).

# About this artifact

The artifact documentation was prepared by using `armada/artifact/prepare.sh`.
The artifact distribution also includes a few scripts from the paper's source
code, for getting lines of code and plotting the scalability numbers.

The VM first does an unattended install of Xubuntu 19.04 using the packer setup
in `armada/artifact/vm`, then we installed all the dependencies (and several
conveniences such as a terminal and ZSH setup) manually.

Finally, we installed the code, which means:

- Clone the Armada and CSPEC repos into the home directory.
- Install the Go dependencies with

    ```
    go get -u github.com/tchajed/goose/...
    go get -u github.com/tchajed/mailboat/...
    ```

  Go clones the source code to `~/go/src/github.com/tchajed/` and also compiles
  and installs the binaries, `goose` and `mailboat-server`.
