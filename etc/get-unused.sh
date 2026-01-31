#!/usr/bin/env bash

set -e

# Resolve project root (assuming script is in etc/)
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PROJECT_ROOT="$(dirname "$DIR")"
cd "$PROJECT_ROOT"

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 <file1.v> [file2.v ...]" >&2
    exit 1
fi

make .rocqdeps.d

# 1. Get list of files used in the build (dependencies)
# We use get-deps.py for each input and union the results.
USED_FILES_TMP=$(mktemp)

for arg in "$@"; do
    if [ ! -f "$arg" ]; then
        echo "Error: File '$arg' not found." >&2
        rm -f "$USED_FILES_TMP"
        exit 1
    fi
    # Canonicalize path
    REL_PATH=$(realpath --relative-to="$PROJECT_ROOT" "$arg")
    # Convert .v to .vo
    VO_PATH="${REL_PATH%.v}.vo"

    # Add the file itself
    echo "$REL_PATH" >> "$USED_FILES_TMP"
    # Add all its recursive dependencies
    ./etc/get-deps.py "$VO_PATH" >> "$USED_FILES_TMP"
done

USED_FILES_SORTED=$(sort -u "$USED_FILES_TMP")
rm -f "$USED_FILES_TMP"

# 2. Get list of all project files
# Matches Makefile ALL_VFILES logic
ALL_FILES=$(find -type f -name "*.v" | sort)

# 3. Compute Set Difference: All - Used = Unused
comm -23 <(echo "$ALL_FILES") <(echo "$USED_FILES_SORTED")
