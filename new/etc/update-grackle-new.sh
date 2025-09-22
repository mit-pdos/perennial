#!/usr/bin/env bash

if [[ -z "$IN_NIX_SHELL" ]]; then
    # Not in nix shell, use the default go installs
    GRACKLE="go run github.com/mjschwenne/grackle/cmd/grackle@latest"
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

# Computes the path within perennial to were the rocq proof should live.
#
# - Replacing "." with "-"
# - Replacing "-" with "_"
perennial_path() {
    echo "$1" | sed -E -e "s/\./-/g" -e "s/-/_/g"
}

# Computes the Rocq logical name by
#
# - Replacing "." with "-"
# - Replacing "-" with "_"
# - Replacing "/" with "."
#
# This mirrors grackle/internal/util/util.go :: CleanCoqName function
rocq_logical_name() {
    echo $(perennial_path "$1") | sed -E -e "s/\//\./g"
}

# Run grackle on the input go package.
#
# We will assume that:
# 1. The proto file is in the directory $2/$1
# 2. We only want to output rocq code
# 3. The rocq code should be output into "new/proof/$1"
# 4. The desired rocq package matches the directory structure
#
# Parameters
# - $1 : Name of the go package inside its repo
# - $2 : Path to the root of the go repo. Go package to translate should be at "$2/$1"
# - $3 : Prefix to compute the go package name, "$3/$1"
run_grackle() {
    $GRACKLE --rocq-logical-path "New.proof.$(rocq_logical_name "$3/$1")" --rocq-physical-path "new/proof/$(perennial_path "$3")/$1" --go-package "$3/$1" "$(realpath "$2/$1")"
}

# Generate Rocq files from gokv repo.
#
# Parameters
# - $1 : Path to the gokv repo.
grackle_gokv() {
    gokv_packages=(
        "cachekv"
        "fencing/ctr"
        "memkv"
        "paxi/comulti"
        "paxi/reconf"
        "reconfig/replica"
        "reconfig/util"
        "tutorial/kvservice"
        "tutorial/lockservice"
        "tutorial/objectstore/chunk"
        "tutorial/objectstore/dir"
        "vrsm/apps/vkv"
        "vrsm/configservice"
        "vrsm/paxos"
        "vrsm/replica"
    )

    for gopkg in "${gokv_packages[@]}"; do
        if ! run_grackle "$gopkg" "$1" "github.com/mit-pdos/gokv"; then
            echo "Failed to run grackle on $gopkg"
            exit 1
        fi
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
                         [--gokv <gokv repo> | -g <gokv repo>] [--help | -h]

Calls grackle on all gokv go modules known to have proto files for grackle usage, generating rocq proofs.

THIS SCRIPT SHOULD BE RUN FROM THE ROOT OF THE PERENNIAL REPO.

--compile-grackle [-c] : Takes the path to the grackle repository, recompiles and installs grackle

--gokv [-g] : Regenerate Rocq proofs for the gokv project, takes path to gokv as argument
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
