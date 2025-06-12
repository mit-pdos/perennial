#!/usr/bin/env bash

if [[ -z "$IN_NIX_SHELL" ]]; then 
    # Not in nix shell, use the default go installs
    GRACKLE="go run github.com/mjschwenne/grackle/cmd/grackle@v1.0"
else 
    # In a nix shell, expect grackle to be on the PATH and use that
    GRACKLE="grackle"
fi

compile_grackle() {
    CWD=$(pwd)
    cd "$1" || return
    go install ./cmd/grackle
    cd "$CWD" || exit
}

# Computes the coq logical name by
#
# - Replacing "." with "-"
# - Replacing "-" with "_"
# - Replacing "/" with "."
#
# This mirrors grackle/internal/util/util.go :: CleanCoqName function
coq_logical_name() {
    echo "$1" | sed -E -e "s/\./-/g" -e "s/-/_/g" -e "s/\//\./g"
}

# Run grackle on the input go package.
#
# We will assume that:
# 1. The proto file is in the directory $2/$1
# 2. We only want to output coq code
# 3. The coq code should be output into "src/program_proof/$1"
# 4. The desired coq package matches the directory structure
#
# Parameters
# - $1 : Name of the go package inside its repo
# - $2 : Path to the root of the go repo. Go package to translate should be at "$2/$1"
# - $3 : Prefix to compute the go package name, "$3/$1"
run_grackle() {
    $GRACKLE --coq-logical-path "Perennial.program_proof.$(coq_logical_name $1)" --coq-physical-path "src/program_proof/$1" --go-package "$3/$1" "$(realpath "$2/$1")"
}

# Generate Coq files from gokv repo.
#
# Parameters
# - $1 : Path to the gokv repo.
grackle_gokv() {
    gokv_packages=(
        "tutorial/kvservice"
        "tutorial/lockservice"
        "tutorial/objectstore/chunk"
        "tutorial/objectstore/dir"
    )

    for gopkg in "${gokv_packages[@]}"; do
        run_grackle "$gopkg" "$1" "github.com/mit-pdos/gokv"
    done
}

ARGS=$(getopt -o "c:g:h" --long "compile-grackle:,gokv:,help" -- "$@")

eval set -- "$ARGS"
while [ $# -ge 1 ]; do
    case "$1" in
    -c | --compile-grackle)
        compile_grackle "$2"
        shift
        ;;
    -g | --gokv)
        grackle_gokv "$2"
        shift
        ;;
    -h | --help)
        cat <<EOF
usage: update-grackle.sh [--compile-grackle <grackle repo> | -c <grackle repo>]
                         [--gokv | -g] [--help | -h]

Calls grackle on all gokv go modules known to have proto files for grackle usage, generating coq proofs.

--compile-grackle [-c] : Takes the path to the grackle repository, recompiles and installs grackle

--gokv [-g] : Regenerate Coq proofs for the gokv project, takes path to gokv as argument
EOF
        shift
        exit 0
        ;;
    --)
        shift
        break
        ;;
    esac
    shift
done
