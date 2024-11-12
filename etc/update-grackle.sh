#!/usr/bin/env bash

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
# 1. The proto file is in the directory $1/$2
# 2. We only want to output coq code
# 3. The coq code should be output into $2
# 4. The desired coq package matches the directory structure
# 5. Grackle is on your $PATH
#
# Parameters
# - $1 : path to go repo with proto files
# - $2 : go package in that repo we're grackling
# - $3 : path to output in perennial
run_grackle() {
    echo grackle --coq-logical-path "Perennial.program_proof.$(coq_logical_name $3)" --coq-physical-path "src/program_proof/$3" "$1/$2"
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
usage: update-grackle.sh [--compile-grackle <grackle repo> | -c <grackle repo>] [--help | -h]

Calls grackle on all gokv go modules known to have proto files for grackle usage, generating coq proofs.

--compile-grackle [-g] : Takes the path to the grackle repository, recompiles and installs grackle
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
        run_grackle "$1" "$gopkg" "program_proof/$gokv"
    done
}
