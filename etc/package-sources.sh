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

if [ "$package" = "all" ]; then
  # get all files
  find src new -not -name "*__nobuild.v" -name "*.v"

elif [ "$package" = "new-goose" ]; then
  # golang.
  find_build src/
  find_build new/golang/
  find_build new/{code,generatedproof}/github_com/goose_lang/goose/model/channel.v
  find_build new/proof/github_com/goose_lang/goose/model/channel
  # go stdlib.
  # TODO: some misplaced files match "new/proof/*.v".
  find_build new/{code,generatedproof,proof,trusted_code,manualproof}/*.v
  find_build new/proof/*_proof
  find_build new/{code,generatedproof,proof}/crypto
  find_build new/{code,generatedproof,proof}/internal
  find_build new/{code,generatedproof}/math
  find_build new/{code,generatedproof,proof,trusted_code,manualproof}/sync
  # common external pkgs.
  find_build new/{code,generatedproof,proof}/github_com/tchajed/marshal.v
  find_build new/{code,generatedproof,proof}/github_com/goose_lang/{std.v,std}
  find_build new/{code,generatedproof,proof,trusted_code,manualproof}/github_com/goose_lang/{primitive.v,primitive}
  # misc.
  find_build new/experiments/glob.v

else
  echo "unknown package $package" 1>&2
  exit 1
fi
