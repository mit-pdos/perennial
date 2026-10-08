#!/usr/bin/env python3
"""Soundness audit of the Lean development: which declarations depend on
`sorryAx` or on non-standard axioms.

Usage: etc/lean-audit.py [--modules ok|all] [-o REPORT] [--json AUDIT.json] [--reuse]

  --modules  ok  (default): import the modules etc/lean-ci.sh recorded as ok in
                 .lake/lean-ci-status.tsv (falls back to `all` if missing)
             all: every Perennial/**/*.lean that has an .olean
  -o         report path (default etc/lean-audit-report.md)
  --json     where to keep the raw output of etc/lean-audit.lean
             (default .lake/lean-audit.json); --reuse skips re-running Lean.

Steps:
 1. `lake env lean --run etc/lean-audit.lean @mods` computes, for every constant
    of a Perennial module, its transitive axioms (as `#print axioms`).
 2. Constants that use `sorryAx` directly are grouped by their user-facing
    declaration ("sorry roots").
 3. Lean `axiom`s and explicit `opaque`s of Perennial modules are listed.
"""
import argparse, collections, json, os, re, subprocess, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
STD_AX = {"propext", "Classical.choice", "Quot.sound"}

ap = argparse.ArgumentParser()
ap.add_argument("--modules", choices=["ok", "all"], default="ok")
ap.add_argument("-o", "--out", default=os.path.join(ROOT, "etc", "lean-audit-report.md"))
ap.add_argument("--json", default=os.path.join(ROOT, ".lake", "lean-audit.json"))
ap.add_argument("--reuse", action="store_true")
args = ap.parse_args()

# ---------------------------------------------------------------- 1. run Lean
status_tsv = os.path.join(ROOT, ".lake", "lean-ci-status.tsv")
ci_rows = []
if os.path.exists(status_tsv):
    for l in open(status_tsv):
        p = l.rstrip("\n").split("\t")
        if len(p) >= 3:
            ci_rows.append(p)

if not args.reuse:
    modlist = os.path.join(ROOT, ".lake", "lean-audit-modules.txt")
    if args.modules == "ok" and ci_rows:
        mods = [r[0] for r in ci_rows if r[2] == "ok"]
    else:
        mods = ["Perennial"]
        for dp, _, fs in os.walk(os.path.join(ROOT, "Perennial")):
            for f in fs:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dp, f), ROOT)[:-5]
                    if os.path.exists(os.path.join(ROOT, ".lake/build/lib/lean", rel + ".olean")):
                        mods.append(rel.replace("/", "."))
    olean = lambda m: os.path.join(ROOT, ".lake/build/lib/lean", m.replace(".", "/") + ".olean")
    missing = [m for m in mods if m != "Perennial" and not os.path.exists(olean(m))]
    if missing:
        print("lean-audit: skipping modules without .olean (being rebuilt?): " + ", ".join(missing), file=sys.stderr)
        open(os.path.join(ROOT, ".lake", "lean-audit-missing.txt"), "w").write("\n".join(missing) + "\n")
    mods = [m for m in mods if m not in missing]
    open(modlist, "w").write("\n".join(sorted(mods)) + "\n")
    print(f"lean-audit: running etc/lean-audit.lean on {len(mods)} modules", file=sys.stderr)
    with open(args.json, "w") as out:
        r = subprocess.run(["lake", "env", "lean", "--run", "etc/lean-audit.lean", "@" + modlist],
                           cwd=ROOT, stdout=out)
    if r.returncode != 0:
        sys.exit(f"etc/lean-audit.lean failed (exit {r.returncode})")

decls, axioms, modules, extsorry = [], [], [], []
modlist_path = os.path.join(ROOT, ".lake", "lean-audit-modules.txt")
nimported = sum(1 for l in open(modlist_path) if l.strip()) if os.path.exists(modlist_path) else len(modules)
for l in open(args.json):
    l = l.strip()
    if not l.startswith("{"):
        continue
    o = json.loads(l)
    {"decl": decls, "axiom": axioms, "module": modules, "extsorry": extsorry}[o["t"]].append(o)

# --------------------------------------------------- 2. sorry roots
roots = {}  # root -> info
for d in decls:
    if not d["direct"] or d["kind"] == "axiom":
        continue
    r = roots.setdefault(d["root"], dict(root=d["root"], module=d["module"], line=0, endLine=0,
                                         synthetic=False, aux=[]))
    if d["name"] == d["root"] or not r["line"]:
        r["line"], r["endLine"] = d["line"], d["endLine"]
    r["synthetic"] |= d["synthetic"]
    if d["name"] != d["root"]:
        r["aux"].append(d["name"])

# ---------------------------------------------------------- 3. Lean axioms
lean_axioms = [d for d in decls if d["kind"] == "axiom"]
all_opaques = [d for d in decls if d["kind"] == "opaque"]
# `partial def`s and `initialize` refs are opaque by construction (meta code)
lean_opaques = [d for d in all_opaques if not d.get("partial") and "._@." not in d["name"]]
nonstd_ext = [a for a in axioms if a["name"] not in STD_AX and a["name"] != "sorryAx"
              and not a["module"].startswith("Perennial")]

# ------------------------------------------------------------- 4. report
tot = dict(decls=0, clean=0, sorry=0, otherAx=0)
for m in modules:
    for k in tot:
        tot[k] += m[k]
def lloc(module, line):
    return f"`{module.replace('.', '/')}.lean:{line}`"

GEN = ("Perennial.Code.", "Perennial.GeneratedProof.")
def generated(m):
    return m.startswith(GEN)

out = []
w = out.append
w("# Lean soundness audit\n")
w("Generated by `etc/lean-ci.sh` + `etc/lean-audit.py` (do not edit by hand).\n")
if ci_rows:
    w("## Build (etc/lean-ci.sh)\n")
    g = collections.defaultdict(collections.Counter)
    for r in ci_rows:
        g[r[1]][r[2]] += 1
    w("| group | ok | FAIL | SKIP |\n|---|---:|---:|---:|")
    for k in ["framework", "code", "genproof", "proof", "other"]:
        if k in g:
            w(f"| {k} | {g[k]['ok']} | {g[k]['FAIL']} | {g[k]['SKIP']} |")
    bad = [r for r in ci_rows if r[2] != "ok"]
    if bad:
        w("\nNot built (excluded from the audit below; FAIL = errors, SKIP = an import failed):\n")
        for r in bad:
            w(f"- {r[2]} `{r[0]}`")
    w("")
w("## Summary\n")
w(f"- Modules audited: {nimported} ({len(modules)} declare constants); Perennial constants: {tot['decls']} "
  f"(incl. auxiliary `_proof_n`/`match_n`/equation lemmas)")
w(f"- Depending only on propext / Classical.choice / Quot.sound: {tot['clean']}")
w(f"- Depending (transitively) on `sorryAx`: {tot['sorry']}")
w(f"- Depending on another non-standard axiom: {tot['otherAx']}")
w(f"- Declarations containing a `sorry` themselves (sorry roots): {len(roots)} "
  f"({sum(r['synthetic'] for r in roots.values())} with a synthetic sorry from an elaboration error)")
w(f"  - in generated modules: {sum(generated(r['module']) for r in roots.values())}")
w(f"- Lean `axiom`s in Perennial: {len(lean_axioms)} "
  f"({sum(generated(a['module']) for a in lean_axioms)} in generated modules)")
w(f"- Lean `opaque` constants in Perennial: {len(all_opaques)} "
  f"({len(all_opaques) - len(lean_opaques)} from `partial def`/`initialize`; {len(lean_opaques)} explicit)")
w(f"- Non-standard axioms from outside Perennial reached by Perennial: "
  + (", ".join(f"`{a['name']}` ({a['module']})" for a in nonstd_ext) or "none"))
w(f"- `sorry`s outside Perennial (iris-lean etc.) reached by Perennial: "
  + (", ".join(f"`{e['name']}` ({e['module']})" for e in extsorry) or "none"))
w("")

w("## Sorry roots (hand-written)\n")
gen_roots = collections.Counter(r["module"] for r in roots.values() if generated(r["module"]))
w(f"{sum(gen_roots.values())} more are in generated modules (the `TypedPointsto`/`IntoValTypedUnderlying` "
  f"instances goose emits with `sorry`) and are only counted per module below.\n")
w("| Lean declaration | Lean source |\n|---|---|")
for r in sorted((r for r in roots.values() if not generated(r["module"])), key=lambda r: (r["module"], r["line"])):
    w(f"| `{r['root']}` | {lloc(r['module'], r['line'])} |")
w("")

w("## Lean axioms (hand-written)\n")
w(f"{sum(generated(a['module']) for a in lean_axioms)} more are in generated modules "
  f"(Perennial/Code, Perennial/GeneratedProof) and are only counted per module below.\n")
w("| Lean axiom | Lean source |\n|---|---|")
for a in sorted((a for a in lean_axioms if not generated(a["module"])), key=lambda a: (a["module"], a["line"])):
    w(f"| `{a['name']}` | {lloc(a['module'], a['line'])} |")
w("")

w("## Lean explicit `opaque` constants\n")
w("Not axioms (an `opaque` needs an `Inhabited` witness, so it cannot introduce "
  "inconsistency), but it hides the definition: listed for review.\n")
w("| Lean opaque | Lean source | axioms |\n|---|---|---|")
for a in sorted(lean_opaques, key=lambda a: (a["module"], a["line"])):
    w(f"| `{a['name']}` | {lloc(a['module'], a['line'])} | {', '.join(a['axioms']) or '-'} |")
w("")

w("## Per module (modules with any non-standard dependency)\n")
w("| module | constants | sorry-dependent | other-axiom-dependent | sorry roots | Lean axioms |\n|---|---:|---:|---:|---:|---:|")
nax = collections.Counter(a["module"] for a in lean_axioms)
nroots = collections.Counter(r["module"] for r in roots.values())
for m in sorted(modules, key=lambda m: m["module"]):
    if m["sorry"] or m["otherAx"]:
        w(f"| `{m['module']}` | {m['decls']} | {m['sorry']} | {m['otherAx']} | {nroots[m['module']]} | {nax[m['module']]} |")
w("")

open(args.out, "w").write("\n".join(out) + "\n")
print(f"wrote {os.path.relpath(args.out, ROOT)}: {len(roots)} sorry roots, {len(lean_axioms)} axioms")
