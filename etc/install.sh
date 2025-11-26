#!/bin/bash

set -eu

# Parse arguments
DEBUG=false
target=""

function show_help() {
	cat <<EOF
Usage: $0 [OPTIONS] TARGET

Run make install using rocq makefile.

OPTIONS:
  --help     Show this help message
  --debug    Generate files but don't install

TARGETS:
  all, new-goose

EOF
	exit 0
}

while [[ $# -gt 0 ]]; do
	case $1 in
	--help)
		show_help
		;;
	--debug)
		DEBUG=true
		shift
		;;
	-*)
		echo "Unknown option: $1" 1>&2
		echo "Use --help for usage information" 1>&2
		exit 1
		;;
	*)
		if [ -z "$target" ]; then
			target="$1"
			shift
		else
			echo "Error: Multiple targets specified" 1>&2
			exit 1
		fi
		;;
	esac
done

if [ -z "$target" ]; then
	echo "Error: No target specified" 1>&2
	echo "Use --help for usage information" 1>&2
	exit 1
fi

function gen_rocq_project() {
	cat _RocqProject
	if [ "$target" = "all" ]; then
		# get all files
		find src new -name "*.v"
	elif [ "$target" = "new-goose" ]; then
		ls src/base.v
		# TODO: program_logic adds a lot of extra files
		find src/Helpers src/algebra src/base_logic src/iris_lib \
			src/program_logic \
			new/golang/{defn/,defn.v} \
			new/golang/{theory/,theory.v} \
            new/proof/sync_proof \
            new/proof/{sync/,sync.v} \
            new/proof/github_com/goose_lang/std.v \
			-not -name "__nobuild.v" \
			-name "*.v"
		ls src/goose_lang/{lang,lifting,locations,notation,ipersist}.v
		ls new/code/github_com/goose_lang/goose/model/channel.v \
			new/{code,trusted_code}/github_com/goose_lang/primitive.v \
			new/code/internal/race.v \
			new/{code,trusted_code}/sync.v \
			new/{code,trusted_code}/sync/atomic.v
		ls new/proof/{proof_prelude,disk_prelude,grove_prelude}.v
	else
		echo "unknown target $target" 1>&2
		exit 1
	fi
}

proj_file=_RocqProject.install
makefile=Makefile.rocq

gen_rocq_project >"$proj_file"
rocq makefile -f "$proj_file" -docroot Perennial -o "$makefile"
#echo "VDFILE:=.rocqdeps.d" >"$makefile.local"

if [ "$DEBUG" = true ]; then
	echo "debug: generated $proj_file and $makefile"
	exit 0
fi

make -j1 -f "$makefile" install

## cleanup
rm -f "$proj_file" \
	"$makefile" "$makefile.conf" "$makefile.local" ".${makefile}.d" \
	.filestoinstall
