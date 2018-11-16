#!/bin/bash

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
