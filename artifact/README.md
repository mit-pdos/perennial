---
title: "Verifying concurrent storage systems with Armada"
---

[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

The code is licensed under the MIT license.

This artifact is licensed under the Creative Commons Attribution license.

# Getting started

The easiest way to use the artifact is to use the provided [VirtualBox
appliance](https://www.dropbox.com/s/tmb9cv8lazuk37c/armada-vm.ova?dl=0). We
have one set of performance numbers that don't reproduce well in a VM, but this
is not the core of the paper's claims. It is also possible to run most of that
experiment using only Go.

Here are some details on the virtual machine:

- The virtual machine appliance is around 3.5GB, and 13GB when extracted.
- The default configuration is 4GB of RAM and two cores. You could get by with
  one core, or can increase these if you want to work in the VM with a graphical
  interface. Only compilation is RAM-intensive.
- The default login is `ubuntu` with no password.
- The default user has sudo access without a password.
- The VM has port forwarding from host port 11737 to SSH in the VM; all you need
  to do is `ssh -p 11737 ubuntu@localhost` to SSH to the virtual machine. You
  can make this more convenient by adding this to your `~/.ssh/config`:
  ```
  # armada artifact VM
  Host armada-vm
    HostName localhost
    Port 11737
    User ubuntu
  ```
  and then using `ssh armada-vm`.
- The default user's shell is a slightly customized zsh.

## Code and dependencies

Here's the code the artifact covers:

- [Armada](https://github.com/mit-pdos/armada), which includes mailboat as an example
- [Goose](https://github.com/tchajed/goose), the translator and Go support libraries
- [Mailboat](https://github.com/tchajed/mailboat) (a Go mail server, written in the Goose subset)

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
  We've compiled Armada, but you can do so yourself by running `make clean-all;
  make -j2`. The build takes around 20 minutes. Compiling Armada only builds the
  proofs and prints the assumptions of the final refinement theorem.

  We also compiled CSPEC.
- Install the Go dependencies with

  ```
  go get -u github.com/tchajed/goose/...
  go get -u github.com/tchajed/mailboat/...
  ```

  Go clones the source code to `~/go/src/github.com/tchajed/` and also compiles
  and installs the binaries, `goose` and `mailboat-server`. We added symlinks to
  the two cloned repos in `~ubuntu`.
- Compiled the artifact documentation within the VM and put the result in
  `~/armada-artifact`. Here you'll find a README.html and EXPERIMENTS.html.

To reduce the file size of the resulting VM, we ran

```sh
# inside VM
sudo apt clean
dd if=/dev/zero of=zeros bs=4M; sync zeros; rm zeros

# on host
VBoxManage modifymedium disk ~/"VirtualBox VMs/armada-vm/armada-vm-disk001.vdi" --compact
```

and finally exported as a VirtualBox appliance:

```sh
VBoxManage export 'armada-vm' -o armada-vm.ova
```
