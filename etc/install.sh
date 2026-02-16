#!/usr/bin/env bash

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

set -eu

# Parse arguments
if [ $# -eq 0 ]; then
	echo "Error: No target specified" 1>&2
	exit 1
fi

target="$1"

function gen_rocq_project() {
	cat _RocqProject
	"$DIR"/package-sources.sh "$target"
}

proj_file=_RocqProject.install
makefile=Makefile.rocq

gen_rocq_project >"$proj_file"
rocq makefile -f "$proj_file" -docroot Perennial -o "$makefile"
#echo "VDFILE:=.rocqdeps.d" >"$makefile.local"

# TODO llm: this currently only supports installing from `.vo` builds. I want
# the option to do a `.vos` build in my local repository, then run
# `opam install . --working-dir --assume-built` to quickly install it to my
# local opam switch, so I can test upstream repos that use perennial. I'm not
# sure what the rocq-generated Makefile does, but perhaps that's what would need
# to change in order to support .vos builds?

make -j1 -f "$makefile" install

## cleanup
rm -f "$proj_file" \
	"$makefile" "$makefile.conf" "$makefile.local" ".${makefile}.d" \
	.filestoinstall
