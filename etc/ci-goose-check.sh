#!/bin/bash
set -e

## Repository pinning

GOOSE_REPO=https://github.com/tchajed/goose/
GOOSE_COMMIT=master

NEW_GOOSE_REPO=https://github.com/upamanyus/goose/
NEW_GOOSE_COMMIT=master

STD_REPO=https://github.com/goose-lang/std
STD_COMMIT=master

MARSHAL_REPO=https://github.com/tchajed/marshal
MARSHAL_COMMIT=master

EXAMPLES_REPO=https://github.com/mit-pdos/perennial-examples
EXAMPLES_COMMIT=master

JOURNAL_REPO=https://github.com/mit-pdos/go-journal
JOURNAL_COMMIT=master

NFSD_REPO=https://github.com/mit-pdos/go-nfsd
NFSD_COMMIT=master

GOKV_REPO=https://github.com/mit-pdos/gokv
GOKV_COMMIT=main

MVCC_REPO=https://github.com/mit-pdos/vmvcc
MVCC_COMMIT=main

# FIXME: need public repo
# RSM_REPO=https://github.com/mit-pdos/rsm
# RSM_COMMIT=main

## Actual test logic

echo && echo "Goose check: fetch all the repos"

function checkout {
  local REPO_VAR=$1_REPO
  local COMMIT_VAR=$1_COMMIT
  local DIR_VAR=$1_DIR

  if [ ! -d ${!DIR_VAR} ] ; then
     git clone "${!REPO_VAR}" "${!DIR_VAR}"
  fi

  (cd "${!DIR_VAR}" && git reset --hard "${!COMMIT_VAR}")
}

GOOSE_DIR=/tmp/goose
checkout GOOSE

NEW_GOOSE_DIR=/tmp/new_goose
checkout NEW_GOOSE

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

MVCC_DIR=/tmp/mvcc
checkout MVCC

# RSM_DIR=/tmp/rsm
# checkout RSM

echo && echo "Goose check: re-run goose"
etc/update-goose.py --goose $GOOSE_DIR --compile \
  --goose-examples \
  --std $STD_DIR \
  --marshal $MARSHAL_DIR \
  --examples $EXAMPLES_DIR \
  --journal $JOURNAL_DIR \
  --nfsd $NFSD_DIR \
  --gokv $GOKV_DIR \
  --mvcc $MVCC_DIR \
# --rsm $RSM_DIR
# Missing: --distributed-examples (not currently used)

echo && echo "Goose check: re-run goose-new"
new/etc/update-goose-new.py --goose $NEW_GOOSE_DIR --compile --gokv $GOKV_DIR

echo && echo "Goose check: check if anything changed"
if [ -n "$(git status --porcelain)" ]; then
  echo 'ERROR: Goose files are not in sync with repositories pinned in `etc/ci-goose-check.sh`. `git diff` after re-goosing:'
  git diff
  exit 1
fi
