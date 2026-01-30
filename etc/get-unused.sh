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

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <file.v>" >&2
    exit 1
fi

TARGET_V="$1"

if [ ! -f "$TARGET_V" ]; then
    echo "Error: File '$TARGET_V' not found." >&2
    exit 1
fi

# Canonicalize target path relative to project root to match Makefile paths
TARGET_V=$(realpath --relative-to="$PROJECT_ROOT" "$TARGET_V")

# Target the .vo file to ensure full compilation dependency graph
TARGET_VO="${TARGET_V%.v}.vo"

# Ensure dependency file exists so make knows the graph
# (Output silenced to avoid noise)
make .rocqdeps.d >/dev/null 2>&1 || true

# 1. Get list of files used in the build (dependencies)
# Run make -Bn (unconditional dry-run) to get the full build plan.
# Grep for the echo command that announces compilation.
# The Makefile uses: @echo "ROCQ COMPILE $<"
# We extract the filename from the echo output.
# usage of .* handles potential leading whitespace in make output
USED_FILES=$(make -Bn "$TARGET_VO" 2>/dev/null | grep 'echo "ROCQ COMPILE ' | sed 's/.*echo "ROCQ COMPILE //; s/"//' | sort -u)

# 2. Get list of all project files
# Matches Makefile ALL_VFILES logic
ALL_FILES=$(find src new -type f -not -name "*__nobuild.v" -name "*.v" | sort)

# 3. Compute Set Difference: All - Used = Unused
comm -23 <(echo "$ALL_FILES") <(echo "$USED_FILES")
