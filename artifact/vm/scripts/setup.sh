#!/bin/bash

set -e

## install dependencies
# artifact dependencies
sudo apt-get install -y opam cloc sqlite3 zip
# conveniences for VM
sudo apt-get install -y virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-utils vim firefox
# CoqIDE dependencies
sudo apt-get install -y pkg-config libgtksourceview2.0-dev

# install Coq
opam init --auto-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released/
opam install -j2 -y coq.8.9.1 coqide
