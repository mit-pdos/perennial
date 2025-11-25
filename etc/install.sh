#!/bin/bash

set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

target=""

if [ $# -gt 0 ]; then
	target="$1"
fi

function gen_rocq_project() {
	cat _RocqProject
	if [ -z "$target" ]; then
		# get all files
		find src new -name "*.v"
	else
		"$DIR"/get-deps.py "$target"
	fi
}

proj_file=_RocqProject.install
makefile=Makefile.rocq

gen_rocq_project >"$proj_file"
rocq makefile -f "$proj_file" -docroot Perennial -o "$makefile"
#echo "VDFILE:=.rocqdeps.d" >"$makefile.local"
make -j1 -f "$makefile" install

## cleanup
rm -f "$proj_file" \
	"$makefile" "$makefile.conf" "$makefile.local" ".${makefile}.d" \
	.filestoinstall
