#!/bin/bash

set -eu

# Parse arguments
if [ $# -eq 0 ]; then
	echo "Error: No target specified" 1>&2
	exit 1
fi

target="$1"

function gen_rocq_project() {
	cat _RocqProject
	etc/package-sources.sh "$target"
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
