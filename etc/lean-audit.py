#!/usr/bin/env python3
"""Soundness audit of the Lean port: which declarations depend on `sorryAx` or
on non-standard axioms, cross-checked against the Rocq sources.

Usage: etc/lean-audit.py [--rocq MASTER_CHECKOUT] [--modules ok|all] [-o REPORT]
                         [--json AUDIT.json] [--reuse]

  --rocq     checkout of master (Rocq sources; default $PERENNIAL_ROCQ or ../perennial-master)
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
    declaration ("sorry roots"); each root is looked up in the Rocq sources
    (same short name; the Rocq file whose path best matches the Lean module
    wins) and classified by how the Rocq proof ends (Qed/Defined vs Admitted vs
    Axiom/Parameter).  A Lean sorry whose Rocq counterpart is proved is a place
    where the port is weaker than Rocq.
 3. Every Lean `axiom` in a Perennial module is checked for a Rocq
    `Axiom`/`Parameter` of the same name.
"""
import argparse, collections, json, os, re, subprocess, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
STD_AX = {"propext", "Classical.choice", "Quot.sound"}

ap = argparse.ArgumentParser()
ap.add_argument("--rocq", default=os.environ.get("PERENNIAL_ROCQ", os.path.join(ROOT, "..", "perennial-master")))
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

# ------------------------------------------------------------ 2. Rocq index
def strip_comments(s):
    out, depth, i, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2; continue
        c = s[i]
        if depth == 0 or c == "\n":
            out.append(c if depth == 0 else "\n")
        i += 1
    return "".join(out)

HDR = re.compile(
    r"^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:(?:Local|Global|Polymorphic|Program|Monomorphic)[ \t]+)*"
    r"(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|CoFixpoint|Instance|"
    r"Example|Axiom|Axioms|Parameter|Parameters|Conjecture|Inductive|Record|Class|Let)[ \t]+"
    r"([A-Za-z_][\w']*)", re.M)
TERM = re.compile(r"\b(Qed|Defined|Admitted|Abort|Save)\s*\.")
MODRE = re.compile(r"^[ \t]*Module[ \t]+(?!Type\b)(?:(?:Import|Export)[ \t]+)?([A-Za-z_][\w']*)(?![\w'])(?![^.]*:=)", re.M)
SECRE = re.compile(r"^[ \t]*Section[ \t]+([A-Za-z_][\w']*)", re.M)
ENDRE = re.compile(r"^[ \t]*End[ \t]+([A-Za-z_][\w']*)[ \t]*\.", re.M)
AXKINDS = {"Axiom", "Axioms", "Parameter", "Parameters", "Conjecture"}

rocq = collections.defaultdict(list)  # name -> [(relpath, line, kind, status, enclosing Modules)]
nrocq = 0
for sub in ("new", "src"):
    base = os.path.join(args.rocq, sub)
    for dp, dns, fs in os.walk(base):
        rel_dp = os.path.relpath(dp, args.rocq)
        if rel_dp.startswith("src/program_proof"):  # old goose: out of scope
            dns[:] = []; continue
        for f in fs:
            if not f.endswith(".v"):
                continue
            path = os.path.join(dp, f)
            rel = os.path.relpath(path, args.rocq)
            s = strip_comments(open(path, errors="ignore").read())
            hdrs = list(HDR.finditer(s))
            terms = [(m.start(), m.group(1)) for m in TERM.finditer(s)]
            # Module/Section nesting, to qualify names (`PrivateKey.t`)
            scopes = sorted([(m.start(), "Module", m.group(1)) for m in MODRE.finditer(s)] +
                            [(m.start(), "Section", m.group(1)) for m in SECRE.finditer(s)] +
                            [(m.start(), "End", m.group(1)) for m in ENDRE.finditer(s)])
            si, stack = 0, []
            ti = 0
            for k, h in enumerate(hdrs):
                while si < len(scopes) and scopes[si][0] < h.start():
                    _, ev, nm = scopes[si]; si += 1
                    if ev == "End":
                        for j in range(len(stack) - 1, -1, -1):
                            if stack[j][1] == nm:
                                del stack[j:]; break
                    else:
                        stack.append((ev, nm))
                qual = tuple(nm for ev, nm in stack if ev == "Module")
                nxt = hdrs[k + 1].start() if k + 1 < len(hdrs) else len(s)
                while ti < len(terms) and terms[ti][0] < h.start():
                    ti += 1
                kind = h.group(1)
                if kind in AXKINDS:
                    st = "Axiom"
                elif ti < len(terms) and terms[ti][0] < nxt:
                    st = terms[ti][1]
                else:
                    st = "def"  # body given directly (`:=`), no proof script
                line = s.count("\n", 0, h.start()) + 1
                rocq[h.group(2)].append((rel, line, kind, st, qual))
                nrocq += 1
                if kind in ("Axioms", "Parameters"):  # `Axioms a b c : T.`
                    rest = s[h.end():s.find(":", h.end())]
                    for extra in rest.split():
                        if re.fullmatch(r"[A-Za-z_][\w']*", extra):
                            rocq[extra].append((rel, line, kind, st, qual))

def snake(seg):
    return re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", seg).lower()

def lean_tokens(module):
    parts = module.split(".")[1:]
    return [snake(p) for p in parts]

def path_score(module, rel):
    lt = lean_tokens(module)
    rt = [p.lower() for p in rel[:-2].split("/")]
    # longest common suffix of path components, then overlap, prefer new/
    suf = 0
    while suf < min(len(lt), len(rt)) and lt[-1 - suf] == rt[-1 - suf]:
        suf += 1
    overlap = len(set(lt) & set(rt))
    return (suf, overlap, rel.startswith("new/"))

def short(name):
    last = re.split(r"\.(?![^«]*»)", name)[-1]
    return last.replace("«", "").replace("»", "")

def lean_parts(name):
    return [p.replace("«", "").replace("»", "") for p in re.split(r"\.(?![^«]*»)", name)]

def qual_score(name, qual):
    lq = [p.replace("'", "") for p in lean_parts(name)[:-1]]
    rq = [p.replace("'", "") for p in qual]
    k = 0
    while k < min(len(lq), len(rq)) and lq[-1 - k] == rq[-1 - k]:
        k += 1
    return k

# Lean names renamed to Lean conventions (etc/lean-rename.py): new -> old
# (Rocq-style) name, so that renamed declarations still find their Rocq
# counterpart
rocq_name = {}
_rn = os.path.join(ROOT, "etc/lean-rename/renames.tsv")
if os.path.exists(_rn):
    for _l in open(_rn, encoding="utf-8"):
        _p = _l.rstrip("\n").split("\t")
        if len(_p) == 2:
            rocq_name[_p[1]] = _p[0]

def rocq_lookup(name, module):
    name = rocq_name.get(name, name)
    sn = short(name)
    cands = rocq.get(sn, []) or rocq.get(sn.replace("'", ""), [])  # Lean renames clashes `Int` -> `Int'`
    if not cands:
        return None, []
    best = max(cands, key=lambda c: (qual_score(name, c[4]), path_score(module, c[0])))
    return best, cands

# --------------------------------------------------- 3. classify sorry roots
def src_of(module):
    return os.path.join(ROOT, module.replace(".", "/") + ".lean")

_src_cache = {}
def src_lines(module):
    if module not in _src_cache:
        p = src_of(module)
        _src_cache[module] = open(p, errors="ignore").read().split("\n") if os.path.exists(p) else []
    return _src_cache[module]

def hint(module, line, end):
    ls = src_lines(module)
    if not line or not ls:
        return ""
    lo, hi = max(0, line - 4), min(len(ls), max(end, line) + 1)
    txt = "\n".join(ls[lo:hi])
    h = []
    if re.search(r"Rocq:\s*Admitted", txt): h.append("Rocq: Admitted")
    if re.search(r"TODO\(port\)", txt): h.append("TODO(port)")
    if re.search(r"Rocq:\s*Axiom", txt, re.I): h.append("Rocq: Axiom")
    return ",".join(h)

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

for r in roots.values():
    r["hint"] = hint(r["module"], r["line"], r["endLine"])
    best, cands = rocq_lookup(r["root"], r["module"])
    r["rocq"] = best
    r["ncands"] = len(cands)
    if best is None:
        r["cls"] = "no-rocq"
    elif best[3] == "Admitted":
        r["cls"] = "ok-admitted"
    elif best[3] == "Axiom":
        r["cls"] = "ok-axiom"
    elif best[3] == "Abort":
        r["cls"] = "ok-admitted"
    else:
        r["cls"] = "MISMATCH"

# ---------------------------------------------------------- 4. Lean axioms
lean_axioms = [d for d in decls if d["kind"] == "axiom"]
for a in lean_axioms:
    best, cands = rocq_lookup(a["name"], a["module"])
    a["rocq"] = best
    a["cls"] = ("no-rocq" if best is None else "ok" if best[3] == "Axiom"
                else "rocq-" + best[3])
all_opaques = [d for d in decls if d["kind"] == "opaque"]
# `partial def`s and `initialize` refs are opaque by construction (meta code)
lean_opaques = [d for d in all_opaques if not d.get("partial") and "._@." not in d["name"]]
for a in lean_opaques:
    best, _ = rocq_lookup(a["name"], a["module"])
    a["rocq"] = best
nonstd_ext = [a for a in axioms if a["name"] not in STD_AX and a["name"] != "sorryAx"
              and not a["module"].startswith("Perennial")]

# ------------------------------------------------------------- 5. report
tot = dict(decls=0, clean=0, sorry=0, otherAx=0)
for m in modules:
    for k in tot:
        tot[k] += m[k]
cls_count = collections.Counter(r["cls"] for r in roots.values())
hint_count = collections.Counter(r["hint"] or "(none)" for r in roots.values())

def rloc(b):
    if not b:
        return "-"
    q = f" in Module {'.'.join(b[4])}" if b[4] else ""
    return f"`{b[0]}:{b[1]}` ({b[2]}{q}, {b[3]})"

def lloc(module, line):
    return f"`{module.replace('.', '/')}.lean:{line}`"

GEN = ("Perennial.Code.", "Perennial.GeneratedProof.")
def generated(m):
    return m.startswith(GEN)

out = []
w = out.append
w("# Lean port soundness audit\n")
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
w("  - Rocq counterpart Admitted/Aborted: %d; Rocq counterpart is an Axiom/Parameter: %d" %
  (cls_count["ok-admitted"], cls_count["ok-axiom"]))
w("  - **Rocq counterpart proved (Qed/Defined/definition): %d** (Lean weaker than Rocq)" % cls_count["MISMATCH"])
w("  - no Rocq declaration of that name found: %d" % cls_count["no-rocq"])
w("  - source hints: " + ", ".join(f"{k}: {v}" for k, v in sorted(hint_count.items())))
w(f"- Lean `axiom`s in Perennial: {len(lean_axioms)} "
  f"({sum(a['cls'] == 'ok' for a in lean_axioms)} with a Rocq Axiom/Parameter of the same name)")
w(f"- Lean `opaque` constants in Perennial: {len(all_opaques)} "
  f"({len(all_opaques) - len(lean_opaques)} from `partial def`/`initialize`; {len(lean_opaques)} explicit)")
w(f"- Non-standard axioms from outside the port reached by Perennial: "
  + (", ".join(f"`{a['name']}` ({a['module']})" for a in nonstd_ext) or "none"))
w(f"- `sorry`s outside the port (iris-lean etc.) reached by Perennial: "
  + (", ".join(f"`{e['name']}` ({e['module']})" for e in extsorry) or "none"))
w(f"- Rocq index: {nrocq} declarations from `new/` and `src/` (without `src/program_proof`)\n")

w("## Mismatches: Lean sorry, Rocq proved\n")
w("Lean declarations that contain `sorry` although the Rocq declaration of the same "
  "name (best path match) ends in `Qed`/`Defined` or is a plain definition. "
  "`TODO(port)` = known unported proof; `Rocq: Admitted` here means the comment is wrong "
  "(or the name match is).\n")
w("| Lean declaration | Lean source | hint | Rocq |\n|---|---|---|---|")
mm = sorted((r for r in roots.values() if r["cls"] == "MISMATCH"), key=lambda r: (r["module"], r["line"]))
for r in mm:
    extra = f" (+{r['ncands']-1} other same-name)" if r["ncands"] > 1 else ""
    w(f"| `{r['root']}` | {lloc(r['module'], r['line'])} | {r['hint'] or '-'} | {rloc(r['rocq'])}{extra} |")
w("")

w("## Lean sorry with no Rocq declaration of the same name\n")
w("Usually Lean-only helpers or renamed/auto-named declarations; review by hand.\n")
w("| Lean declaration | Lean source | hint |\n|---|---|---|")
for r in sorted((r for r in roots.values() if r["cls"] == "no-rocq"), key=lambda r: (r["module"], r["line"])):
    w(f"| `{r['root']}` | {lloc(r['module'], r['line'])} | {r['hint'] or '-'} |")
w("")

w("## Lean axioms\n")
ngen_ok = collections.Counter(a["module"] for a in lean_axioms if a["cls"] == "ok" and generated(a["module"]))
w(f"{sum(ngen_ok.values())} axioms in generated modules (Perennial/Code, Perennial/GeneratedProof) "
  f"match a Rocq Axiom and are only counted per module below; all others are listed.\n")
w("| Lean axiom | Lean source | Rocq | status |\n|---|---|---|---|")
for a in sorted((a for a in lean_axioms if not (a["cls"] == "ok" and generated(a["module"]))),
                key=lambda a: (a["cls"] == "ok", a["module"], a["line"])):
    st = "ok" if a["cls"] == "ok" else f"**{a['cls']}**"
    w(f"| `{a['name']}` | {lloc(a['module'], a['line'])} | {rloc(a['rocq'])} | {st} |")
w("")

w("## Lean explicit `opaque` constants\n")
w("Not axioms (an `opaque` needs an `Inhabited` witness, so it cannot introduce "
  "inconsistency), but it hides the definition: listed for review against Rocq.\n")
w("| Lean opaque | Lean source | axioms | Rocq |\n|---|---|---|---|")
for a in sorted(lean_opaques, key=lambda a: (a["module"], a["line"])):
    w(f"| `{a['name']}` | {lloc(a['module'], a['line'])} | {', '.join(a['axioms']) or '-'} | {rloc(a['rocq'])} |")
w("")

w("## Lean sorry matching a Rocq Admitted / Axiom\n")
gen_ok = collections.Counter(r["module"] for r in roots.values() if r["cls"].startswith("ok") and generated(r["module"]))
w(f"{sum(gen_ok.values())} of these are in generated modules (the `TypedPointsto`/`IntoValTypedUnderlying` "
  f"instances goose emits as Admitted) and are only counted per module below; the hand-written ones:\n")
w("| Lean declaration | Lean source | hint | Rocq |\n|---|---|---|---|")
for r in sorted((r for r in roots.values() if r["cls"].startswith("ok") and not generated(r["module"])),
                key=lambda r: (r["module"], r["line"])):
    w(f"| `{r['root']}` | {lloc(r['module'], r['line'])} | {r['hint'] or '-'} | {rloc(r['rocq'])} |")
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
print(f"wrote {os.path.relpath(args.out, ROOT)}: {len(roots)} sorry roots "
      f"({cls_count['MISMATCH']} Rocq-proved, {cls_count['no-rocq']} no Rocq match), "
      f"{len(lean_axioms)} axioms ({sum(a['cls'] != 'ok' for a in lean_axioms)} without Rocq Axiom)")
