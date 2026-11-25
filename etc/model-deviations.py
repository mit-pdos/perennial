#!/usr/bin/env python3
"""Count the `MODEL:` markers of the Go model overlays: how many places a Go model
departs from the real Go source (R12 of .agents/skills/review-trusted/SKILL.md;
goose/model-overlays-plan.md). A measure of the trust base, printed by
`etc/land.sh prepare`; no gate.

A marker is an occurrence of `MODEL:` in a non-test `.go` file. A package is the
file's directory relative to the overlay root (`internal/sync`, `time`, ...).

Usage: etc/model-deviations.py [DIR ...]
    Perennial's goose/model/overlay, then each DIR (another repository's models, e.g.
    etcd-grove's `models/`). With no DIR, `$ETCD_GROVE_DIR/models` is added when
    ETCD_GROVE_DIR is set and the directory exists.
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PERENNIAL_OVERLAY = os.path.join(ROOT, "goose", "model", "overlay")


def count(root):
    """{package: markers} for the overlay tree at `root`."""
    per = {}
    for d, dirs, files in os.walk(root):
        dirs[:] = sorted(x for x in dirs if not x.startswith(".") and x != "testdata")
        for f in files:
            if not f.endswith(".go") or f.endswith("_test.go"):
                continue
            with open(os.path.join(d, f), encoding="utf-8", errors="replace") as fh:
                n = fh.read().count("MODEL:")
            if n:
                pkg = os.path.relpath(d, root).replace(os.sep, "/")
                per[pkg] = per.get(pkg, 0) + n
    return per


def report(label, root):
    per = count(root)
    total = sum(per.values())
    print(f"MODEL: markers in {label}: {total} in {len(per)} package(s)")
    for pkg in sorted(per):
        print(f"  {per[pkg]:4d}  {pkg}")
    return total


def main(argv):
    if any(a in ("-h", "--help") for a in argv):
        print(__doc__.strip())
        return 0
    extra = list(argv)
    if not extra:
        eg = os.environ.get("ETCD_GROVE_DIR")
        if eg and os.path.isdir(os.path.join(eg, "models")):
            extra.append(os.path.join(eg, "models"))
    report("goose/model/overlay", PERENNIAL_OVERLAY)
    for d in extra:
        if not os.path.isdir(d):
            print(f"model-deviations: {d}: not a directory (skipped)", file=sys.stderr)
            continue
        report(d, d)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
