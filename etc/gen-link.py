#!/usr/bin/env python3
"""Generate the `Link.lean` of every proved Go package, and check the layout of
`Perennial/Spec` and `Perennial/Proof` (docs/PERENNIAL_PROOF_REFERENCE.md, "Layout of
the program proofs").

Every Go function or method `F` of a package `P` (a directory, the Go import path
with `.`, `/` and `-` replaced as in `Perennial/Code`) has

* `Perennial/Spec/P/F.lean`, holding its one Hoare triple, `abbrev <F>.spec : Prop`;
* `Perennial/Proof/P/F.lean`, holding `theorem <F>.wp_proof (callee specs) : <F>.spec`
  (or `axiom <F>.wp_proof : <F>.spec` at the trust boundary), which imports only
  the `Spec` files of its callees.

The file name `F` is the function's name, `T__M` for a method `M` of `T` (either
receiver), and `initialize` for the package's `initialize'`. The spec's name is
written in full below `Perennial` (`sync.Mutex.Lock.spec`), and ends in the
components of `F` (`Mutex.Lock`).

This script writes `Perennial/Proof/P/Link.lean`, which instantiates every proof of
`P` with its callees' results, in dependency order:

    theorem sync.Mutex.wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG) :=
      sync.Mutex.Lock.wp_proof

the result of `<pre>.<f>.spec` being `<pre>.wp_<f>`. A callee of another package
is that package's result, from its `Link.lean`. The callees are read from the
hypotheses of `wp_proof`, `(name : <G>.spec ...)`, in order.

usage: etc/gen-link.py           regenerate every Link.lean
       etc/gen-link.py --check   exit 1 if a Link.lean is out of date or the layout
                                 is broken (nothing is written)
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, "Perennial", "Spec")
PROOF = os.path.join(ROOT, "Perennial", "Proof")
# Files of a package directory that are not a Go function's.
SHARED_OK = re.compile(r"^[A-Z][A-Za-z0-9]*$")

NAME = r"[A-Za-z_«][A-Za-z0-9_'.«»!?]*"
SPEC_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:abbrev|def)\s+(" + NAME + r")\.spec\b", re.M)
PROOF_DECL = re.compile(r"^\s*(theorem|axiom)\s+(" + NAME + r")\.wp_proof\b", re.M)
HYP = re.compile(r"\(\s*(" + NAME + r")\s*:\s*(" + NAME + r")\.spec\b")

errors = []


def err(msg):
    errors.append(msg)


def rel(path):
    return os.path.relpath(path, ROOT)


def lean_files(base):
    for d, _, fs in os.walk(base):
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def module_of(path):
    return ".".join(os.path.relpath(path[: -len(".lean")], ROOT).split(os.sep))


def strip_guillemets(s):
    return s.replace("«", "").replace("»", "")


def components(name):
    # split a Lean name on dots outside «»
    out, cur, quoted = [], "", False
    for c in name:
        if c == "«":
            quoted = True
        elif c == "»":
            quoted = False
        if c == "." and not quoted:
            out.append(cur)
            cur = ""
        else:
            cur += c
    out.append(cur)
    return out


def check_file_name(path, name):
    """`F` (the file name) is the last components of `name`, joined by `__`."""
    f = os.path.basename(path)[: -len(".lean")]
    parts = [strip_guillemets(c) for c in components(name)]
    if parts[-1] == "initialize'":
        parts[-1] = "initialize"
    want = f.split("__")
    if parts[-len(want):] != want:
        err(f"{rel(path)}: the file of `{name}` should be named after it "
            f"(`{'__'.join(parts[-2:])}.lean` for a method, `{parts[-1]}.lean` for a function)")


def result_name(spec):
    cs = components(spec)
    return ".".join(cs[:-1] + ["wp_" + cs[-1]])


def proof_signature(text, start):
    """The text from `theorem X.wp_proof` to its `:=` (or the end of the axiom's statement)."""
    m = re.compile(r":=|\n\s*\n").search(text, start)
    return text[start : m.start() if m else len(text)]


def main():
    check = "--check" in sys.argv[1:]

    # specs: name -> (package dir, file)
    specs = {}
    for path in lean_files(SPEC):
        text = open(path, encoding="utf-8").read()
        names = SPEC_DECL.findall(text)
        if len(names) != 1:
            err(f"{rel(path)}: a Spec file holds exactly one `<fn>.spec` (found {len(names)})")
            continue
        name = names[0]
        check_file_name(path, name)
        pkg = os.path.relpath(os.path.dirname(path), SPEC)
        specs[name] = (pkg, path)

    # proofs, by package: name -> (file, hypotheses [(hyp name, callee spec)])
    packages = {}
    for path in lean_files(PROOF):
        text = open(path, encoding="utf-8").read()
        decls = list(PROOF_DECL.finditer(text))
        if not decls:
            continue
        if len(decls) != 1:
            err(f"{rel(path)}: a Proof file holds exactly one `<fn>.wp_proof` (found {len(decls)})")
            continue
        d = decls[0]
        name = d.group(2)
        pkg = os.path.relpath(os.path.dirname(path), PROOF)
        spec_path = os.path.join(SPEC, os.path.relpath(path, PROOF))
        if specs.get(name, (None, None))[1] != spec_path:
            err(f"{rel(path)}: `{name}.wp_proof` has no spec `{name}.spec` in {rel(spec_path)}")
        sig = proof_signature(text, d.start())
        hyps = HYP.findall(sig)
        variables = re.findall(r"^open .*$|^variable .*$", text, re.M)
        packages.setdefault(pkg, {})[name] = (path, hyps, variables)

    for name, (pkg, path) in specs.items():
        if name not in packages.get(pkg, {}):
            err(f"{rel(path)}: `{name}.spec` has no proof in "
                f"{rel(os.path.join(PROOF, os.path.relpath(path, SPEC)))}")

    outputs = {}
    for pkg, proofs in sorted(packages.items()):
        # dependency order within the package
        order, state = [], {}

        def visit(n, stack):
            if state.get(n) == "done":
                return
            if state.get(n) == "active":
                err(f"package {pkg}: the proofs' hypotheses are circular: {' -> '.join(stack + [n])}")
                return
            state[n] = "active"
            for _, callee in proofs[n][1]:
                if callee in proofs:
                    visit(callee, stack + [n])
            state[n] = "done"
            order.append(n)

        for n in sorted(proofs):
            visit(n, [])

        imports, variables = set(), []
        for n in order:
            path, hyps, vs = proofs[n]
            imports.add(module_of(path))
            for v in vs:
                if v not in variables:
                    variables.append(v)
            for hname, callee in hyps:
                if callee not in specs:
                    err(f"{rel(path)}: hypothesis `{hname}`: no Spec file defines `{callee}.spec`")
                    continue
                cpkg = specs[callee][0]
                if cpkg != pkg:
                    imports.add(module_of(os.path.join(PROOF, cpkg, "Link.lean")))

        lines = [
            "/-",
            f"The results of the proofs of `{pkg}`: every `<F>.wp_proof` of",
            f"`Perennial/Proof/{pkg}/` applied to its callees' results, in dependency order.",
            "Generated by `etc/gen-link.py`; do not edit by hand.",
            "-/",
            "module",
            "",
        ]
        lines += [f"public import {m}" for m in sorted(imports)]
        lines += ["", "@[expose] public section", "", "namespace Perennial", ""]
        lines += [v for v in variables if v.startswith("open ")]
        lines += ["", "section link"]
        lines += [v for v in variables if v.startswith("variable ")]
        for n in order:
            _, hyps, _ = proofs[n]
            r = result_name(n)
            args = "".join(f" {result_name(c)}" for _, c in hyps)
            lines += ["", f"theorem {r} : {n}.spec (GF := GF) (hG := hG) :=",
                      f"  {n}.wp_proof{args}"]
        lines += ["", "end link", "", "end Perennial", ""]
        outputs[os.path.join(PROOF, pkg, "Link.lean")] = "\n".join(lines)

    # Link files of packages that no longer have proofs
    for path in lean_files(PROOF):
        if os.path.basename(path) == "Link.lean" and path not in outputs:
            err(f"{rel(path)}: a Link.lean for a package with no proofs")

    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        sys.exit(1)

    stale = []
    for path, content in sorted(outputs.items()):
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != content:
            stale.append(path)
            if not check:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(content)
    for p in stale:
        print(("out of date: " if check else "wrote ") + rel(p))
    if check and stale:
        sys.exit(1)


if __name__ == "__main__":
    main()
