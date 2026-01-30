#!/usr/bin/env bash

set -e

# Resolve project root (assuming script is in etc/)
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PROJECT_ROOT="$(dirname "$DIR")"

if [ ! -f "$PROJECT_ROOT/Makefile" ]; then
    echo "Error: Makefile not found in $PROJECT_ROOT. Run this script from the project root or ensure it is in etc/." >&2
    exit 1
fi

cd "$PROJECT_ROOT"

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 <file1.v> [file2.v ...]" >&2
    exit 1
fi

TARGET_VOS=""

for arg in "$@"; do
    if [ ! -f "$arg" ]; then
        echo "Error: File '$arg' not found." >&2
        exit 1
    fi
    # Canonicalize path
    REL_PATH=$(realpath --relative-to="$PROJECT_ROOT" "$arg")
    # Convert .v to .vo
    VO_PATH="${REL_PATH%.v}.vo"
    TARGET_VOS="$TARGET_VOS $VO_PATH"
done

# Ensure dependency file exists so make knows the graph
# (Output silenced to avoid noise)
make .rocqdeps.d >/dev/null 2>&1 || true

# 1. Get list of files used in the build (dependencies)
# Run make -Bn (unconditional dry-run) to get the full build plan.
# Grep for the echo command that announces compilation.
# The Makefile uses: @echo "ROCQ COMPILE $<"
# We extract the filename from the echo output.
# usage of .* handles potential leading whitespace in make output
# passing multiple targets to make will build the union of their dependencies
USED_FILES=$(make -Bn $TARGET_VOS 2>/dev/null | grep 'echo "ROCQ COMPILE ' | sed 's/.*echo "ROCQ COMPILE //; s/"//' | sort -u)

# 2. Get list of all project files
# Matches Makefile ALL_VFILES logic
ALL_FILES=$(find src new -type f -not -name "*__nobuild.v" -name "*.v" | sort)

# 3. Compute Set Difference: All - Used = Unused
comm -23 <(echo "$ALL_FILES") <(echo "$USED_FILES")