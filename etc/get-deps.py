#!/usr/bin/env python3
"""
Script to recursively find all .vo dependencies from .rocqdeps.d Makefile dependencies.
Outputs all dependencies with .vo extension changed to .v
"""

import sys
import os


def parse_rocqdeps(deps_file):
    """
    Parse a .rocqdeps.d file and return a dictionary mapping targets to their dependencies.
    Handles multiple targets on the left-hand side of a rule.

    Returns:
        dict: mapping from target to list of dependencies
    """
    deps_map = {}

    if not os.path.exists(deps_file):
        return deps_map

    with open(deps_file, "r") as f:
        content = f.read()

    # Process each rule (may span multiple lines with backslash continuation)
    lines = content.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # Skip empty lines and comments
        if not line or line.startswith("#"):
            i += 1
            continue

        # Accumulate lines that end with backslash
        while line.endswith("\\") and i + 1 < len(lines):
            i += 1
            line = line[:-1] + " " + lines[i].strip()

        # Check if this is a dependency rule (contains colon)
        if ":" in line:
            parts = line.split(":", 1)
            targets_str = parts[0].strip()
            deps_str = parts[1].strip() if len(parts) > 1 else ""

            # Split targets and dependencies
            targets = targets_str.split()
            deps = deps_str.split()

            # Map each target to its dependencies
            for target in targets:
                if target not in deps_map:
                    deps_map[target] = []
                deps_map[target].extend(deps)

        i += 1

    return deps_map


def get_recursive_vo_deps(target, deps_map, visited=None):
    """
    Recursively find all .vo dependencies of a target.

    Args:
        target: the target to find dependencies for
        deps_map: dictionary mapping targets to dependencies
        visited: set of already visited targets (to avoid cycles)

    Returns:
        set: all .vo dependencies
    """
    if visited is None:
        visited = set()

    # Avoid infinite loops
    if target in visited:
        return set()

    visited.add(target)
    vo_deps = set()

    # Get direct dependencies
    if target in deps_map:
        for dep in deps_map[target]:
            # If dependency ends in .vo, add it to results
            if dep.endswith(".vo"):
                vo_deps.add(dep)

            # Recursively get dependencies of this dependency
            vo_deps.update(get_recursive_vo_deps(dep, deps_map, visited))

    return vo_deps


def main():
    if len(sys.argv) != 2:
        print("Usage: get-deps.py <target>", file=sys.stderr)
        sys.exit(1)

    target = sys.argv[1]
    deps_file = ".rocqdeps.d"

    # Parse the dependencies file
    deps_map = parse_rocqdeps(deps_file)

    # Get all recursive .vo dependencies
    vo_deps = get_recursive_vo_deps(target, deps_map)

    # Convert .vo to .v and output
    v_deps = sorted([dep[:-2] + "v" for dep in vo_deps])

    for dep in v_deps:
        print(dep)


if __name__ == "__main__":
    main()
