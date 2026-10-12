#!/usr/bin/env python3
"""Generate the `Link.lean` of every proved Go package, and check the layout of
`Perennial/Spec` and `Perennial/Proof` (docs/PERENNIAL_PROOF_REFERENCE.md, "Layout of
the program proofs").

Every Go function or method `F` of a package `P` (a directory, the package's path as
under `Perennial/Code`) has

* `Perennial/Spec/P/F.lean`, holding its one Hoare triple, `abbrev <F>.spec : Prop`;
* `Perennial/Proof/P/F.lean`, holding `theorem <F>.wp_proof (callee specs) : <F>.spec`
  (or `axiom <F>.wp_proof : <F>.spec` at the trust boundary), which imports only
  the `Spec` files of its callees and shared files.

The file name `F` is the function's name, `T__M` for a method `M` of `T` (either
receiver), `initialize` for the package's `initialize'` (and in general without the
`'` goose appends to a name that clashes, `Index` for `Index'`), with a trailing `_` for
the lower-case one of two names that differ only in case (`asType_` next to `AsType`,
for case-insensitive file systems). The spec's name is
written in full below `Perennial` (`sync.Mutex.Lock.spec`), and ends in the
components of `F` (`Mutex.Lock`).

This script writes `Perennial/Proof/P/Link.lean`, which instantiates every proof of
`P` with its callees' results, in dependency order:

    theorem sync.Mutex.wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG) :=
      sync.Mutex.Lock.wp_proof

the result of `<pre>.<f>.spec` being `<pre>.wp_<f>`. A callee of another package
is that package's result, from its `Link.lean`. The callees are read from the
hypotheses of `wp_proof`, `(name : <G>.spec ...)`, in order.

It also checks the imports: a Spec file, a Proof file or a shared file of a package
imports no Proof file of a Go function, no `Link.lean` and no package umbrella
(`Perennial/Proof/P.lean`, for a package `P` with a `Link.lean`).

usage: etc/gen-link.py [PKG...]           regenerate every Link.lean (or those of the
                                          package directories PKG, e.g. `sync/atomic`)
       etc/gen-link.py --check [PKG...]   exit 1 if a Link.lean is out of date or the
                                          layout is broken (nothing is written)
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, "Perennial", "Spec")
PROOF = os.path.join(ROOT, "Perennial", "Proof")

NAME = r"[A-Za-z_«][A-Za-z0-9_'.«»!?]*"
SPEC_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:abbrev|def)\s+(" + NAME + r")\.spec\b", re.M)
PROOF_DECL = re.compile(r"^\s*(theorem|axiom)\s+(" + NAME + r")\.wp_proof\b", re.M)
HYP = re.compile(r"\(\s*(" + NAME + r")\s*:\s*(" + NAME + r")\.spec\b")
VAR_BINDER = re.compile(r"[({\[]\s*([A-Za-z_][\w'\s]*?)\s*:")
IMPORT = re.compile(r"^(?:public )?import (Perennial\.Proof\.\S+)", re.M)

errors = []


def err(msg, pkg=None):
    errors.append((pkg, msg))


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
    """A Lean name's components (dots inside «» do not split)."""
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


def check_file_name(path, name, pkg):
    """`F` (the file name) is the last components of `name`, joined by `__`."""
    f = os.path.basename(path)[: -len(".lean")]
    parts = [strip_guillemets(c) for c in components(name)]
    # goose primes a Go name that clashes with a Lean one (`initialize'`, `Index'`); the
    # file has the Go name
    if parts[-1].endswith("'"):
        parts[-1] = parts[-1][:-1]
    # a trailing `_` keeps apart names that differ only in case (`asType_.lean` next to
    # `AsType.lean`), for case-insensitive file systems
    want = (f[:-1] if f.endswith("_") and not f.endswith("__") else f).split("__")
    if parts[-len(want):] != want:
        err(f"{rel(path)}: the file of `{name}` should be named after it "
            f"(`{'__'.join(parts[-2:])}.lean` for a method, `{parts[-1]}.lean` for a "
            f"function)", pkg)


def result_name(spec):
    cs = components(spec)
    # `wp_` + a quoted keyword is an ordinary identifier (`sort.«Sort»` -> `sort.wp_Sort`)
    return ".".join(cs[:-1] + ["wp_" + strip_guillemets(cs[-1])])


def proof_signature(text, start):
    """The text from `theorem X.wp_proof` to its `:=` (or the end of the axiom's statement)."""
    # the `:=` outside brackets (not the `(GF := GF)` of a hypothesis)
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and (text.startswith(":=", i) or text.startswith("\n\n", i)):
            return text[start:i]
    return text[start:]


def main():
    argv = sys.argv[1:]
    check = "--check" in argv
    selected = {a.strip("/") for a in argv if not a.startswith("--")}

    # specs: name -> (package dir, file)
    specs = {}
    for path in lean_files(SPEC):
        text = open(path, encoding="utf-8").read()
        names = SPEC_DECL.findall(text)
        pkg = os.path.relpath(os.path.dirname(path), SPEC)
        if len(names) != 1:
            err(f"{rel(path)}: a Spec file holds exactly one `<fn>.spec` (found {len(names)})", pkg)
            continue
        name = names[0]
        check_file_name(path, name, pkg)
        specs[name] = (pkg, path)

    # proofs, by package: name -> (file, hypotheses [(hyp name, callee spec)], open/variable lines)
    packages = {}
    for path in lean_files(PROOF):
        text = open(path, encoding="utf-8").read()
        decls = list(PROOF_DECL.finditer(text))
        if not decls:
            continue
        pkg = os.path.relpath(os.path.dirname(path), PROOF)
        if len(decls) != 1:
            err(f"{rel(path)}: a Proof file holds exactly one `<fn>.wp_proof` "
                f"(found {len(decls)})", pkg)
            continue
        d = decls[0]
        name = d.group(2)
        spec_path = os.path.join(SPEC, os.path.relpath(path, PROOF))
        if specs.get(name, (None, None))[1] != spec_path:
            err(f"{rel(path)}: `{name}.wp_proof` has no spec `{name}.spec` in "
                f"{rel(spec_path)}", pkg)
        hyps = HYP.findall(proof_signature(text, d.start()))
        # section-level `open`s and `variable`s (not `open … in`, which scopes one declaration)
        context = [l for l in re.findall(r"^open .*$|^variable .*$", text, re.M)
                   if not l.rstrip().endswith(" in")]
        packages.setdefault(pkg, {})[name] = (path, hyps, context)

    for name, (pkg, path) in specs.items():
        if name not in packages.get(pkg, {}):
            err(f"{rel(path)}: `{name}.spec` has no proof in "
                f"{rel(os.path.join(PROOF, os.path.relpath(path, SPEC)))}", pkg)

    # the imports of the discipline
    fn_proofs = {module_of(p) for ps in packages.values() for (p, _, _) in ps.values()}
    links = {module_of(os.path.join(PROOF, pkg, "Link.lean")) for pkg in packages}
    umbrellas = {module_of(os.path.join(PROOF, pkg + ".lean")) for pkg in packages}
    for base in (SPEC, PROOF):
        for path in lean_files(base):
            pkg = os.path.relpath(os.path.dirname(path), base)
            if base == PROOF:
                if pkg not in packages:
                    continue  # not a package of this layout (yet), or an umbrella
                if (os.path.basename(path) in ("Link.lean", "Results.lean")
                        or module_of(path) in umbrellas):
                    continue
                # a shared file is UpperCamelCase; a lower-case file that is not a
                # function's proof is another package's module not in this layout yet
                if module_of(path) not in fn_proofs and not os.path.basename(path)[0].isupper():
                    continue
            for imp in IMPORT.findall(open(path, encoding="utf-8").read()):
                imp = strip_guillemets(imp)
                if imp in fn_proofs or imp in links or imp in umbrellas:
                    err(f"{rel(path)}: imports {imp}; import the Spec files of callees "
                        f"and shared files only", pkg)

    # file names that differ only in case clash on case-insensitive file systems
    for base in (SPEC, PROOF):
        for d, _, fs in os.walk(base):
            seen = {}
            for f in fs:
                if f.lower() in seen:
                    err(f"{rel(os.path.join(d, f))}: clashes with {seen[f.lower()]} on a "
                        f"case-insensitive file system; add a trailing `_` to the "
                        f"lower-case name", os.path.relpath(d, base))
                seen[f.lower()] = f

    outputs = {}
    for pkg, proofs in sorted(packages.items()):
        if selected and pkg not in selected:
            continue
        # dependency order within the package
        order, state = [], {}

        def visit(n, stack):
            if state.get(n) == "done":
                return
            if state.get(n) == "active":
                err(f"package {pkg}: the proofs' hypotheses are circular: "
                    f"{' -> '.join(stack + [n])}", pkg)
                return
            state[n] = "active"
            for _, callee in proofs[n][1]:
                if callee in proofs:
                    visit(callee, stack + [n])
            state[n] = "done"
            order.append(n)

        for n in sorted(proofs):
            visit(n, [])

        imports, context = set(), []
        for n in order:
            path, hyps, ctx = proofs[n]
            imports.add(module_of(path))
            for v in ctx:
                if v not in context:
                    context.append(v)
            for hname, callee in hyps:
                if callee not in specs:
                    err(f"{rel(path)}: hypothesis `{hname}`: no Spec file defines "
                        f"`{callee}.spec`", pkg)
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
        lines += [v for v in context if v.startswith("open ")]
        # One `section link` with the union of the proofs' `variable`s, unless two of
        # them declare a binder differently (e.g. `[hG : HeapGS HasLC.hasLC GF]` for a
        # proof that needs later credits): then a section per run of proofs with the
        # same `variable`s, each with that proof file's own.
        def own_vars(n):
            return [v for v in proofs[n][2] if v.startswith("variable ")]
        binders = {}
        for v in context:
            if v.startswith("variable "):
                for names in VAR_BINDER.findall(v):
                    for b in names.split():
                        binders.setdefault(b, set()).add(v)
        if any(len(vs) > 1 for vs in binders.values()):
            runs = []
            for n in order:
                if runs and own_vars(runs[-1][-1]) == own_vars(n):
                    runs[-1].append(n)
                else:
                    runs.append([n])
            sections = [(own_vars(r[0]), r) for r in runs]
        else:
            sections = [([v for v in context if v.startswith("variable ")], order)]
        for i, (vs, ns) in enumerate(sections):
            if i > 0:
                lines += ["", "end link", ""]
            else:
                lines += [""]
            lines += ["section link"]
            lines += vs
            for n in ns:
                _, hyps, _ = proofs[n]
                args = "".join(f" {result_name(c)}" for _, c in hyps)
                lines += ["", f"theorem {result_name(n)} : {n}.spec (GF := GF) (hG := hG) :=",
                          f"  {n}.wp_proof{args}"]
        lines += ["", "end link", "", "end Perennial", ""]
        outputs[os.path.join(PROOF, pkg, "Link.lean")] = "\n".join(lines)

    # Link files of packages that no longer have proofs
    for path in lean_files(PROOF):
        pkg = os.path.relpath(os.path.dirname(path), PROOF)
        if os.path.basename(path) == "Link.lean" and pkg not in packages:
            err(f"{rel(path)}: a Link.lean for a package with no proofs", pkg)

    if selected:
        errors[:] = [(p, m) for (p, m) in errors if p is None or p in selected]
    if errors:
        for _, e in errors:
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
