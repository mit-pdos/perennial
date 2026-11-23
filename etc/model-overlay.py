#!/usr/bin/env python3
"""The Go-model overlay of the standard library (goose/model/overlay/overlay.toml).

Usage: etc/model-overlay.py json [-o FILE]   write the overlay for goose (go build -overlay format)
       etc/model-overlay.py check            check the models against the real files (exit 1 if not)
       etc/model-overlay.py test [GO_TEST_ARGS...]
                                             the difftest: run the real standard-library tests of
                                             each entry's `tests` with the models in place

Each entry of overlay.toml replaces whole files of a standard-library package by the model files
of the same name in goose/model/overlay/<path>/. `json` maps $GOROOT/src/<path>/<file> to the
model file (GOROOT from `go env GOROOT`: the toolchain the standard library is translated from),
for goose, proofgen, skiplint and modelcheck (etc/update-goose-new.py --std-lib). `test` adds the
entry's `asm` files, replaced by an empty assembly file, so that the package builds with the
models' Go bodies instead of the assembly, and runs `go test -overlay` on the entry's `tests`.

`check` makes sure a model replaces what it claims: each replaced file exists, and the model file
has the same build constraint and declares exactly the same top-level functions, with the same
signatures, as the real one.
"""
import json, os, re, subprocess, sys, tempfile, tomllib

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
MODEL_DIR = os.path.join(ROOT, "goose", "model", "overlay")
CONFIG = os.path.join(MODEL_DIR, "overlay.toml")


def goroot():
    return subprocess.run(["go", "env", "GOROOT"], check=True, capture_output=True,
                          text=True).stdout.strip()


def entries():
    with open(CONFIG, "rb") as f:
        return tomllib.load(f).get("package", [])


def replacements(root, with_asm, empty_asm=None):
    """The overlay map {real file: replacement}."""
    ov = {}
    for e in entries():
        for name in e["replace"]:
            ov[os.path.join(root, "src", e["path"], name)] = os.path.join(MODEL_DIR, e["path"], name)
        if with_asm:
            for name in e.get("asm", []):
                ov[os.path.join(root, "src", e["path"], name)] = empty_asm
    return ov


def write_json(ov, out):
    with open(out, "w") as f:
        json.dump({"Replace": ov}, f, indent=1, sort_keys=True)
        f.write("\n")


FUNC = re.compile(r"^func\s+(\([^)]*\)\s*)?(\w+)\s*(\[[^\]]*\])?\s*\(", re.M)


def decls(src):
    """The top-level function declarations of a Go file: name -> signature text."""
    out = {}
    for m in FUNC.finditer(src):
        line = src[m.start():src.index("\n", m.start())]
        sig = line.rstrip().removesuffix("{").strip()
        out[(m.group(1) or "").strip() + m.group(2)] = re.sub(r"\s+", " ", sig)
    return out


def build_line(src):
    m = re.search(r"^//go:build .*$", src, re.M)
    return m.group(0) if m else None


def check():
    root = goroot()
    ok = True
    for real, model in replacements(root, with_asm=False).items():
        if not os.path.isfile(real):
            print(f"{real}: the replaced file does not exist"); ok = False; continue
        if not os.path.isfile(model):
            print(f"{model}: the model file does not exist"); ok = False; continue
        rs, ms = open(real).read(), open(model).read()
        if build_line(rs) != build_line(ms):
            print(f"{model}: build constraint {build_line(ms)!r}, the real file's {build_line(rs)!r}")
            ok = False
        rd, md = decls(rs), decls(ms)
        if rd != md:
            print(f"{model}: declares {sorted(md.values())}, the real file {sorted(rd.values())}")
            ok = False
        for other in re.findall(r"^(?:var|const|type)\s+(\w+)", ms, re.M):
            print(f"{model}: declares {other}, which a file replacement may not add"); ok = False
    for e in entries():
        for name in e.get("asm", []):
            p = os.path.join(root, "src", e["path"], name)
            if not os.path.isfile(p):
                print(f"{p}: the replaced assembly file does not exist"); ok = False
    return ok


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__); return 0
    cmd, rest = argv[0], argv[1:]
    if cmd == "json":
        out = rest[1] if rest[:1] == ["-o"] and len(rest) == 2 else None
        ov = replacements(goroot(), with_asm=False)
        if out is None:
            json.dump({"Replace": ov}, sys.stdout, indent=1, sort_keys=True); print()
        else:
            write_json(ov, out)
        return 0
    if cmd == "check":
        return 0 if check() else 1
    if cmd == "test":
        if not check():
            return 1
        with tempfile.TemporaryDirectory(prefix="model-overlay-") as d:
            empty = os.path.join(d, "empty.s")
            with open(empty, "w") as f:
                f.write('#include "textflag.h"\n')
            ovf = os.path.join(d, "overlay.json")
            write_json(replacements(goroot(), with_asm=True, empty_asm=empty), ovf)
            tests = sorted({t for e in entries() for t in e.get("tests", [])})
            return subprocess.run(["go", "test", "-overlay", ovf] + rest + tests, cwd=d).returncode
    print(f"unknown command {cmd!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
