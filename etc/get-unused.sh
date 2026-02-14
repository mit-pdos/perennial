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

USED_FILES_TMP=$(mktemp)
ALL_FILES_TMP=$(mktemp)

# Clean up on exit
# trap 'rm -f "$USED_FILES_TMP" "$ALL_FILES_TMP"' EXIT

# 1. Get list of all project files
find -type f -name "*.v" -printf "%P\n" | sort > "$ALL_FILES_TMP"
echo "DONE"

# 2. Get list of files used in the build (dependencies)
for arg in "$@"; do
    if [ ! -f "$arg" ]; then
        echo "Error: File '$arg' not found." >&2
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

# Sort and unique the used files
# We sort into a new temp file to avoid reading/writing to same file in pipe
USED_FILES_SORTED_TMP=$(mktemp)
sort -u "$USED_FILES_TMP" > "$USED_FILES_SORTED_TMP"
mv "$USED_FILES_SORTED_TMP" "$USED_FILES_TMP"

# 3. Compute Set Difference: All - Used = Unused
comm -3 "$ALL_FILES_TMP" "$USED_FILES_TMP"
