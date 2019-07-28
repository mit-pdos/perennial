#!/bin/bash

set -e

## install dependencies
# artifact dependencies
sudo apt-get install -y opam cloc sqlite3 zip
# conveniences for VM
sudo apt-get install -y virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-utils vim firefox
# CoqIDE dependencies
sudo apt-get install -y pkg-config libgtksourceview2.0-dev
