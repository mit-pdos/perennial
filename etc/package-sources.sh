#!/bin/bash

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

if [ "$package" = "all" ]; then
  # get all files
  find src new -not -name "*__nobuild.v" -name "*.v"
elif [ "$package" = "new-goose" ]; then
  ls src/base.v
  # TODO: program_logic adds a lot of extra files
  find src/Helpers src/algebra src/base_logic src/iris_lib \
    src/program_logic \
    new/golang/{defn/,defn.v} \
    new/golang/{theory/,theory.v} \
    new/proof/sync_proof \
    new/proof/{sync/,sync.v} \
    new/proof/github_com/goose_lang/std.v \
    -not -name "*__nobuild.v" \
    -name "*.v"
  ls -1 src/goose_lang/{lang,lifting,locations,notation,ipersist}.v
  ls -1 new/code/github_com/goose_lang/goose/model/channel.v \
    new/{code,trusted_code}/github_com/goose_lang/primitive.v \
    new/code/internal/race.v \
    new/{code,trusted_code}/sync.v \
    new/{code,trusted_code}/sync/atomic.v
  ls -1 new/proof/{proof_prelude,disk_prelude,grove_prelude}.v
else
  echo "unknown package $package" 1>&2
  exit 1
fi
