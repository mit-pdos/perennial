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
  find "$@" -not -name "*__nobuild.v" -name "*.v" -print
}

if [ "$package" = "all" ]; then
  # get all files
  find src new -not -name "*__nobuild.v" -name "*.v"

elif [ "$package" = "new-goose" ]; then
  # golang.
  find_build src/
  find_build new/ -type d -name go_etcd_io -prune -o

else
  echo "unknown package $package" 1>&2
  exit 1
fi
