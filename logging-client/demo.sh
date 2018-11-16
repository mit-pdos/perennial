#!/bin/bash

# Demo of using write-ahead logging over a replicated disk.
#
# To build the dependencies:
# 1. run `make extract` at the root (this requires Coq)
# 2. run `stack setup` to install a sandboxed GHC (this uses the Haskell Tool Stack)
# 3. run `stack build` to compile the logging-cli binary
#
# The replicated disk is simulated using two files disk0.img and disk1.img,
# which are initialized to 1MB each internally, then initialized by the
# replication implementation, and finally initialized by the logging
# implementation.
#
# The logging-cli exposes the logging API as subcommands, including a call to
# recovery. This demo demonstrates using this API.

set -e

log() {
  echo "> $@"
  stack exec -- logging-cli "$@"
}

log init

echo "# basic interaction"
log read 0
log write 0 10
echo "## reads use the persistent state"
log read 0
log write 1 12
log write 3 15
echo "## out-of-bounds writes silently do nothing"
log write 1000000000 15
log commit
log recover
log read 0
log read 1
log read 3
log read 1000000000

echo
echo "# aborting a transaction, replication"
log write 1 12
log write 3 25
echo '## "fail" one of the disks'
echo "rm disk0.img"
rm disk0.img
log write 100 7
echo "## to simulate a crash we run recovery"
log recover
log read 0
log read 1
log read 3
log read 100

echo
echo "## cleanup"
echo "rm disk1.img"
rm "disk1.img"
