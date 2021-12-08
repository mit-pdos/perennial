#!/bin/bash
set -e

## Repository pinning

GOOSE_REPO=https://github.com/tchajed/goose/
GOOSE_COMMIT=194a438

STD_REPO=https://github.com/goose-lang/std
STD_COMMIT=21c4593d3dec287058496318f724f67c23b6ab43

MARSHAL_REPO=https://github.com/tchajed/marshal
MARSHAL_COMMIT=c83ef7fef021044dd066c60adb197d8e5b1657d1

EXAMPLES_REPO=https://github.com/mit-pdos/perennial-examples
EXAMPLES_COMMIT=e851a931fe93455088a8ceab0b2de3f2986bc15a

JOURNAL_REPO=https://github.com/mit-pdos/go-journal
JOURNAL_COMMIT=5c187da39e0cc7f566cfac1ba6d87b33e6cf4ece

NFSD_REPO=https://github.com/mit-pdos/goose-nfsd
NFSD_COMMIT=cc2916878dd43ef8929a0dd0258b0214f08f58f3

GOKV_REPO=https://github.com/mit-pdos/gokv.git
GOKV_COMMIT=4af64f65dc1f27691c0fb4c270f6751908983ce5

## Actual test logic

echo && echo "Goose check: fetch all the repos"

function checkout {
  local REPO_VAR=$1_REPO
  local COMMIT_VAR=$1_COMMIT
  local DIR_VAR=$1_DIR

  git clone "${!REPO_VAR}" "${!DIR_VAR}"
  (cd "${!DIR_VAR}" && git reset --hard "${!COMMIT_VAR}")
}

GOOSE_DIR=/tmp/goose
checkout GOOSE

STD_DIR=/tmp/std
checkout STD

MARSHAL_DIR=/tmp/marshal
checkout MARSHAL

EXAMPLES_DIR=/tmp/examples
checkout EXAMPLES

JOURNAL_DIR=/tmp/journal
checkout JOURNAL

NFSD_DIR=/tmp/nfsd
checkout NFSD

GOKV_DIR=/tmp/gokv
checkout GOKV

echo && echo "Goose check: re-run goose"
etc/update-goose.py --goose $GOOSE_DIR --compile \
  --std $STD_DIR \
  --marshal $MARSHAL_DIR \
  --examples $EXAMPLES_DIR \
  --journal $JOURNAL_DIR \
  --nfsd $NFSD_DIR \
  --gokv $GOKV_DIR
# Missing: --distributed-examples (not currently used), --mvcc (very WIP)

echo && echo "Goose check: check if anything changed"
if [ -n "$(git status --porcelain)" ]; then
  echo 'ERROR: Goose files are not in sync with repositories pinned in `etc/ci-goose-check.sh`. `git diff` after re-goosing:'
  git diff
  exit 1
fi
