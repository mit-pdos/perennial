#!/usr/bin/env bash

set -eu

function show_help() {
  cat <<EOF
Usage: $0 PACKAGE

List source files for a given package.

PACKAGES:
  all        All .v files in src and new directories
  new-goose  Specific subset of files for new-goose package

OPTIONS:
  --help     Show this help message

EOF
  exit 0
}

if [ $# -eq 0 ]; then
  echo "Error: No package specified" 1>&2
  echo "Use --help for usage information" 1>&2
  exit 1
fi

if [ "$1" = "--help" ]; then
  show_help
fi

package="$1"

function find_build() {
  find "$@" -not -name "*__nobuild.v" -name "*.v"
}

function goose_common() {
  ls -1 src/base.v
  # TODO: program_logic adds a lot of extra files
  find_build src/Helpers src/algebra src/base_logic src/iris_lib \
    src/program_logic
}

if [ "$package" = "all" ]; then
  # get all files
  find src new -not -name "*__nobuild.v" -name "*.v"
elif [ "$package" = "new-goose" ]; then
  goose_common
  ls -1 \
    src/goose_lang/{lang,lifting,locations,notation,ipersist}.v
  find_build \
    new/golang/{defn/,defn.v} \
    new/golang/{theory/,theory.v} \
    new/{atomic_fupd,grove_prelude}.v \
    new/proof/sync_proof \
    new/proof/{sync/,sync.v} \
    new/proof/github_com/goose_lang/std.v
  ls -1 new/code/github_com/goose_lang/goose/model/channel.v \
    new/{code,trusted_code}/github_com/goose_lang/primitive.v \
    new/experiments/{chan,glob}.v \
    new/code/internal/race.v \
    new/{code,trusted_code}/sync.v \
    new/{code,trusted_code}/sync/atomic.v \
    new/proof/{proof_prelude,grove_prelude}.v
  # standard library (subset; some standard library is in directories)
  ls -1 new/{code,generatedproof,proof}/*.v
  ls -1 new/{code,generatedproof}/{internal,math}/*.v
  ls -1 new/proof/internal/*.v
  ls -1 new/proof/github_com/tchajed/marshal.v
  ls -1 new/{code,generatedproof,proof}/github_com/goose_lang/{std.v,std/std_core.v}
  find_build new/{generatedproof,manualproof,trusted_code}
  find_build new/proof/github_com/goose_lang/goose/model/channel
  ls -1 new/proof/github_com/goose_lang/primitive.v
elif [ "$package" = "old-goose" ]; then
  goose_common
  find_build src/goose_lang
  #ls -1 \
  #  src/goose_lang/{prelude,base_prelude,proofmode,tactics,wpc_proofmode}.v \
  #  src/goose_lang/{adequacy,array,typing,crash_modality}.v
  #find_build src/goose_lang/ffi/ src/goose_lang/lib/
  find_build external/Goose/github_com/goose_lang
  ls -1 external/Goose/github_com/mit_pdos/gokv/{erpc,urpc}.v
  ls -1 external/Goose/github_com/tchajed/marshal.v
  ls -1 \
    src/program_proof/unittest.v \
    src/program_proof/{proof_prelude,disk_lib,disk_prelude,grove_prelude}.v \
    src/program_proof/marshal*.v \
    src/program_proof/std_proof.v
  find_build src/program_proof/grove_shared/
else
  echo "unknown package $package" 1>&2
  exit 1
fi
