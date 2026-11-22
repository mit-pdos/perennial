#!/usr/bin/env python3
"""Trust delta of a change: which trusted files it touches and what it adds to
the trusted base. Input to the `review-trusted` skill
(.agents/skills/review-trusted/SKILL.md); it does not judge, it reports.

Usage: etc/trusted-delta.py [TARGET] [--full] [--no-diff] [--check]
       etc/trusted-delta.py --self-test

  TARGET     a commit (reviews that commit: COMMIT^..COMMIT), a range A..B, or
             nothing: the working tree against the merge base with origin/lean
             (committed and uncommitted work of the current branch)
  --full     print the diff of every changed file, not only the trusted ones
  --no-diff  print only the summary and the signal lines
  --check    exit 1 if the change touches the trusted base (tier 0) at all,
             for use in hooks
  --self-test  check the signal patterns on built-in examples and exit

Skipped package variables: for every variable a goose config newly lists in a
`[[skip]]` entry (or `skip = [...]`), it prints the reason and the variable's
Go source (`go doc -u -src`).

Tiers (see the skill): 0 = trusted (semantics, translator, trusted models,
goose configuration); 1 = generated (trusted through goose; hand edits are
suspect); 2 = program logic and libraries (proved, but can hide trust in an
axiom/sorry/opaque); 3 = proofs, docs, tooling.

For every added line the report flags *signals*: constructs that add to or
move the trusted base (assume, axiom, sorry, opaque, native_decide, ...) and
constructs that change what the model does (Panic, AngelicExit, a new step
rule, a new trusted `.impl`, a `trusted =` list, ...). A step rule takes many
forms (`⟦i, a⟧ ⤳ e`, `⤳[t]`, `is_go_step_pure i a = fun e => ...`,
`go.IsGoStepPureDet[Tagged] ...`, `IsGoStep`, `FuncUnfold`/`MethodUnfold`, a
`BaseStep` constructor, or an `instance` of any of them); in a tier-0 file, a
changed line anywhere inside such a declaration (a rule's continuation lines,
e.g. the body of a relational `is_go_step_pure` rule) is flagged too, with the
declaration it belongs to. For a new or changed
trusted model whose docstring quotes Go code, it prints the real Go source of
the function (`go doc -src`) next to it, when the Go toolchain can find it.
"""
import os, re, subprocess, sys, tomllib

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

# --------------------------------------------------------------- tiers
TIER0 = [
    ("semantics", r"^Perennial/GooseLang/(Lang|BoundedLang|Adequacy|Threads|Receipts|Locations|Ext|CrashLang|CrashAdequacy|DistLang|DistAdequacy|InitAdequacy)\.lean$"),
    ("semantics", r"^Perennial/GooseLang/Ext/"),
    ("semantics", r"^Perennial/Golang/Defn(/|\.lean$)"),
    ("semantics", r"^Perennial/GrovePrelude\.lean$"),
    ("translator", r"^goose/.*\.go$"),
    ("translator-gold", r"^goose/testdata/.*\.gold\.lean$"),
    ("go-model", r"^goose/model/"),
    ("trusted-model", r"^Perennial/TrustedCode/"),
    ("goose-config", r"^Perennial/Code/.*\.toml$"),
]
TIER1 = [
    ("generated-code", r"^Perennial/Code/.*\.lean$"),
    ("generated-proof", r"^Perennial/GeneratedProof/"),
]
TIER2 = [
    ("logic", r"^Perennial/GooseLang/"),
    ("logic", r"^Perennial/Golang/Theory/"),
    ("library", r"^Perennial/(Std|Algebra|Ghost|IrisLib|Helpers)/"),
    ("library", r"^Perennial/Ghost\.lean$"),
]

def tier_of(path):
    for t, rules in ((0, TIER0), (1, TIER1), (2, TIER2)):
        for kind, rx in rules:
            if re.search(rx, path):
                return t, kind
    return 3, "other"

# --------------------------------------------------------------- signals
# Declaration modifiers that may precede a keyword: `@[simp] private noncomputable axiom ...`.
MODS = r"^\s*(@\[[^\]]*\]\s*)*((noncomputable|private|protected|scoped|local|public|unsafe|partial)\s+)*"

# Every syntactic form of a Go step rule: the `⤳` notation (`⤳`, `⤳[tag]`), the
# relation it abbreviates written out (`IsGoStepPureDet`, `IsGoStepPureDetTagged`),
# an equation on the relation itself (`is_go_step_pure i a = fun e => ...`, how
# nondeterministic rules are stated), the full step `IsGoStep`, an unfolding of a
# Go function or method, and the base step relation of GooseLang.
STEP_RULE = (r"⤳|\bis_go_step_pure\b|\bIsGoStepPureDet(Tagged)?\b|\bIsGoStep\b"
             r"|HeadStep|base_step|BaseStep|\b(Func|Method)Unfold\b")

# (name, regex on an added/removed line, why it matters)
SIGNALS = [
    ("axiom", MODS + r"axiom\b", "a new axiom: trusted outright"),
    ("sorry", r"\bsorry\b|\bsorryAx\b", "an unproved obligation; in tiers 0-2 it is an axiom"),
    ("opaque", MODS + r"opaque\b", "an opaque constant: a value nobody can inspect"),
    ("native", r"native_decide|bv_decide|ofReduceBool|Lean\.ofReduceBool", "trusts native code (forbidden by README)"),
    ("implemented_by", r"implemented_by|@\[extern|\bextern\s+\"", "runtime behaviour differs from the definition"),
    ("unsafe", r"^\s*unsafe\s+(def|theorem)|\bunsafe\s+(def|instance|opaque|abbrev)\b", "Lean unsafe definition"),
    ("partial", MODS + r"partial\s+def\b|\bpartial\s+def\b", "partial def: an opaque constant in disguise"),
    ("assume", r"\bassume\b|\w*[aA]ssume(No|Mul|Sum)\w*", "a model assumption: must be unreachable in Go (README, Model assumptions)"),
    ("angelic", r"AngelicExit", "an angelic exit: the model refuses to continue (sound only if Go cannot reach it)"),
    ("panic", r"\bPanic\s+\"|Panic \(|\bgo\.panic\b|PanicV", "a (stuck) run-time panic in the model"),
    ("step-rule", STEP_RULE, "a semantics rule or unfolding (any form: `⤳`, `is_go_step_pure`, "
     "`IsGoStepPureDet`, `FuncUnfold`, ...; in tier 0 also a changed line inside one)"),
    ("semantics-class", r"^\s*class\s+\w*Semantics\b|" + MODS +
     r"instance\b.*:\s*(\w+\.)*(\w*Semantics|GoLocalContext|GoGlobalContext|GooseExts)\b",
     "a semantics class, or an instance of one (or of the contexts defining `is_go_step_pure`)"),
    ("adequacy", r"\bgoose_(adequacy|invariance|init)\w*\b|GooseGpreS|receiptBound|threadBound", "an adequacy theorem or its parameters"),
    ("trusted-impl", r"\.impl\w*\s*(\[.*\])?\s*:\s*val\b|\.implWith\b", "a hand-written model of Go code"),
    ("trusted-list", r"^\s*trusted\s*=|^\s*\"!|^\s*translate\s*=|trust_proofgen|^\s*axiomatize\s*=", "goose configuration: what is trusted/translated/axiomatized"),
    ("skip-list", r"^\s*\[\[skip\]\]|^\s*skip\s*=", "goose configuration: package variables not translated at all (trusted: not running each initializer is unobservable)"),
    ("global-var-addr", r'GlobalVarAddr\s*\(?\s*go!"', "the address of a package variable by its literal name: the one way hand-written code can reach a variable goose skips (the name has no Lean declaration)"),
    ("extension", r"\bExtSemantics\b|\bGooseSemantics\b|\bextStep\w*|\bGooseExt\b", "an extension's semantics (new primitive operations)"),
    ("set_option", r"^\s*set_option\b", "an option change (linters off, max heartbeats, ...)"),
    ("verbatim", r"VerbatimExpr|Verbatim", "goose emits Lean text verbatim"),
]

# Outside tier 0, at most this many lines of each signal are listed per file.
COLLAPSE = 8

def is_prose(path, text):
    """Comment, markdown or toml-comment line: signals there are words, not code."""
    if path.endswith(".md"):
        return True
    t = text.lstrip()
    return t.startswith(("--", "/-", "-/", "#", "* ", "| ")) or (path.endswith(".toml") and t.startswith("#"))

def signals_in(line):
    out = []
    for name, rx, why in SIGNALS:
        if re.search(rx, line):
            out.append((name, why))
    return out

def decl_statements(content):
    """Split Lean source into declarations, so that a changed continuation line can be
    attributed to the step rule it belongs to. A declaration starts at a code line of
    indentation 0, or, inside a `class`/`structure`/`inductive` (whose fields and
    constructors are the semantics' rules), of indentation <= 2.
    -> (stmt index of each line (0-based), [(head line number (1-based), code text)],
        whether each line holds code (not only comment))."""
    lines = content.split("\n")
    ids, stmts, is_code = [], [], []
    in_comment, container = 0, False
    for i, line in enumerate(lines):
        t = line.strip()
        code = ""
        if in_comment:
            if "-/" in line:
                in_comment = 0
                code = line.split("-/", 1)[1].strip()
        elif t.startswith("/-"):
            if "-/" not in t[2:]:
                in_comment = 1
            else:
                code = t[2:].split("-/", 1)[1].strip()
        elif not t.startswith("--"):
            code = re.sub(r"\s--.*$", "", line).rstrip()
        if code:
            ind = len(line) - len(line.lstrip())
            if ind == 0:
                container = bool(re.match(MODS + r"(class\s+)?(class|structure|inductive)\b", line))
            if ind == 0 or (container and ind <= 2) or not stmts:
                stmts.append((i + 1, ""))
            n, txt = stmts[-1]
            stmts[-1] = (n, txt + "\n" + code)
        ids.append(max(len(stmts) - 1, 0))
        is_code.append(bool(code))
    return ids, stmts, is_code

# --------------------------------------------------------------- git
def git(*args, check=True):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"git {' '.join(args)} failed:\n{r.stderr}")
    return r.stdout

def resolve_target(argv):
    """Return (description, diff_args, rev_for_show_new, rev_for_show_old)."""
    if not argv:
        mb = git("merge-base", "origin/lean", "HEAD").strip()
        return (f"working tree vs merge-base with origin/lean ({mb[:9]})", [mb], None, mb)
    t = argv[0]
    if ".." in t:
        a, b = t.split("..", 1)
        b = b.lstrip(".") or "HEAD"
        a = a.lstrip(".")
        return (f"range {a}..{b}", [a, b], b, a)
    sha = git("rev-parse", "--verify", t + "^{commit}").strip()
    subj = git("log", "-1", "--format=%h %s", sha).strip()
    return (f"commit {subj}", [sha + "^", sha], sha, sha + "^")

def parse_diff(diff_args):
    """-> {path: {"status": s, "hunks": [(new_lineno, '+'/'-', text)], "raw": str}}"""
    raw = git("diff", "--no-color", "-U3", "--no-ext-diff", *diff_args, "--")
    files, cur = {}, None
    new_ln, old_ln, in_comment = 0, 0, False
    for line in raw.split("\n"):
        if line.startswith("diff --git"):
            m = re.match(r"diff --git a/(.*) b/(.*)$", line)
            path = m.group(2)
            cur = files[path] = {"status": "M", "lines": [], "old": [], "raw": [line]}
            in_comment = False
            continue
        if cur is None:
            continue
        cur["raw"].append(line)
        if line[:1] in "+- " and not line.startswith(("+++", "---")):
            text = line[1:]
            prose = in_comment or is_prose(path, text)
            if "/-" in text and "-/" not in text.split("/-", 1)[1]:
                in_comment = True
            elif "-/" in text:
                in_comment = False
        else:
            prose = False
        if line.startswith("new file mode"):
            cur["status"] = "A"
        elif line.startswith("deleted file mode"):
            cur["status"] = "D"
        elif line.startswith("rename to"):
            cur["status"] = "R"
        elif line.startswith("@@"):
            m = re.match(r"@@ -(\d+)(?:,\d+)? \+(\d+)", line)
            old_ln, new_ln = int(m.group(1)), int(m.group(2))
        elif line.startswith("+") and not line.startswith("+++"):
            cur["lines"].append((new_ln, "+", line[1:], prose))
            cur["old"].append(None)
            new_ln += 1
        elif line.startswith("-") and not line.startswith("---"):
            cur["lines"].append((new_ln, "-", line[1:], prose))
            cur["old"].append(old_ln)
            old_ln += 1
        elif line.startswith(" "):
            new_ln += 1
            old_ln += 1
    for f in files.values():
        f["raw"] = "\n".join(f["raw"])
    return files

def file_at(rev, path):
    """Content of `path` at `rev` (None: the working tree); '' if absent."""
    if rev is None:
        try:
            return open(os.path.join(ROOT, path)).read()
        except OSError:
            return ""
    r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""

def step_rule_context_hits(path, f, rev_old, rev_new):
    """Changed code lines of a tier-0 Lean file that lie inside a declaration containing a
    step rule but do not themselves name one (e.g. the `fun e => ...` body of a relational
    `is_go_step_pure` rule): one hit per declaration and side, unless the change already
    names the rule on one of its own lines. -> [(ln, sign, name, text)]"""
    if not path.endswith(".lean"):
        return []
    sides = {"+": decl_statements(file_at(rev_new, path)), "-": decl_statements(file_at(rev_old, path))}
    direct, ctx = set(), {}
    for (ln, s, text, prose), oln in zip(f["lines"], f["old"]):
        if prose:
            continue
        ln = ln if s == "+" else oln
        idx = ln - 1
        ids, stmts, is_code = sides[s]
        # a docstring line whose `/--` lies outside the hunk is still prose
        if not (0 <= idx < len(ids)) or not stmts or not is_code[idx]:
            continue
        sid = ids[idx]
        if re.search(STEP_RULE, text):
            direct.add((s, sid))
        elif re.search(STEP_RULE, stmts[sid][1]) and (s, sid) not in ctx:
            head = stmts[sid][1].strip().split("\n", 1)[0].strip()
            ctx[(s, sid)] = (ln, s, "step-rule",
                             f"{text.strip()}  [in the rule at line {stmts[sid][0]}: {head[:80]}]")
    return [h for k, h in ctx.items() if k not in direct]

# --------------------------------------------------------------- Go source lookup
def go_source(symbol, unexported=False):
    """`go doc -src strings.Split` (`-u` also for unexported names); '' if the
    toolchain cannot find it."""
    # read-only: never let `go doc` rewrite go.sum / go.work.sum
    env = dict(os.environ, GOFLAGS="-mod=readonly", GOWORK="off")
    try:
        r = subprocess.run(["go", "doc"] + (["-u"] if unexported else []) + ["-src", symbol], cwd=ROOT, capture_output=True,
                           text=True, timeout=60, env=env)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return r.stdout if r.returncode == 0 else ""

def trusted_impls(path, files, rev):
    """Names of `.impl`s added/changed in a TrustedCode file -> (go symbol, docstring Go block)."""
    added = [t for _, s, t, _ in files[path]["lines"] if s == "+"]
    names = []
    for t in added:
        m = re.match(r"\s*(?:noncomputable\s+)?def\s+([\w.«»']+)\.impl\w*\b", t)
        if m:
            n = m.group(1).replace("«", "").replace("»", "")
            if n not in names:
                names.append(n)
    if not names:
        return []
    # package = namespace of the file (Perennial/TrustedCode/<pkg path>.lean)
    pkg = re.sub(r"^Perennial/TrustedCode/|\.lean$", "", path)
    pkg = pkg.replace("_com/", ".com/").replace("_org/", ".org/").replace("_io/", ".io/")
    try:
        content = git("show", f"{rev}:{path}") if rev else open(os.path.join(ROOT, path)).read()
    except SystemExit:
        content = ""
    out = []
    for n in names:
        gosym = f"{pkg}.{n.replace('.', '.')}"
        # docstring just before the def, if any
        block = ""
        m = re.search(r"/--((?:(?!-/).)*?)-/\s*(?:noncomputable\s+)?def\s+" + re.escape(n) + r"\.impl", content, re.S)
        if m:
            g = re.search(r"```go\n(.*?)```", m.group(1), re.S)
            block = g.group(1) if g else ""
        out.append((n, gosym, block))
    return out

def toml_lists(path, rev_old, rev_new):
    """The pattern lists of a goose config, old and new: [(key, added, removed)].
    `skip` maps each skipped name to its reason; its items are `name` strings
    (skip_reasons gives the reasons)."""
    def show(rev):
        if rev is None:
            try:
                return open(os.path.join(ROOT, path)).read()
            except OSError:
                return ""
        r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else ""
    old, new = goose_lists(show(rev_old)), goose_lists(show(rev_new))
    out = []
    for key in sorted(set(old) | set(new)):
        o, n = old.get(key, []), new.get(key, [])
        if o != n:
            out.append((key, [x for x in n if x not in o], [x for x in o if x not in n]))
    return out, skip_reasons(show(rev_new)), skip_reasons(show(rev_old))

def parse_config(text):
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        print(f"(could not parse the goose config: {e})")
        return {}

def goose_lists(text):
    c = parse_config(text)
    d = {}
    for key in ("translate", "trusted", "axiomatize", "imports"):
        if key in c:
            d[key] = [str(x) for x in c[key]]
    if "trust_proofgen" in c:
        d["trust_proofgen"] = [str(c["trust_proofgen"])]
    if "skip" in c:
        d["skip"] = [n for e in c["skip"] for n in e.get("names", [])]
    return d

def skip_reasons(text):
    return {n: e.get("reason", "") for e in parse_config(text).get("skip", []) for n in e.get("names", [])}

def config_pkg(path):
    """The Go package of a goose config Perennial/Code/<pkg>.toml."""
    pkg = os.path.relpath(path, "Perennial/Code")[: -len(".toml")]
    return pkg.replace("_com/", ".com/").replace("_org/", ".org/").replace("_io/", ".io/")

# --------------------------------------------------------------- self-test
def self_test():
    """The signal patterns on examples of every form they are meant to catch (and a few
    they must not). Run by `etc/trusted-delta.py --self-test`."""
    must = {
        "step-rule": [
            "  neg_float64 (v : w64) : ⟦GoUnOp GoNeg go.float64, #v⟧ ⤳[under] #(float64Neg v)",
            "  eq (v : w64) : ⟦GoOp GoEquals go.float64, (#v, #v)⟧ ⤳ #true",
            "    is_go_step_pure (GoOp GoPlus t) glv((#v1, #v2)) =",
            "  go_prealloc_step : is_go_step_pure GoPrealloc #() =",
            "    go.IsGoStepPureDet InternalMapLookupId (PairV (map.mapV dv es) id)",
            "instance foo : go.IsGoStepPureDetTagged under (GoOp GoPlus t) v e := ⟨⟨h⟩⟩",
            "  len_chan : FuncUnfold go.len [t] f",
            "  m : MethodUnfold t \"Len\" f",
            "  | RecS f x e σg : BaseStep (Rec f x e) σg [] (Val (RecV f x e)) σg []",
        ],
        "axiom": ["axiom foo : False", "private axiom foo : False", "@[simp] noncomputable axiom x : Nat"],
        "opaque": ["opaque f : Nat → Nat", "@[implemented_by g] private opaque f : Nat"],
        "implemented_by": ["@[implemented_by fast] def f := 1", "@[extern \"lean_f\"] opaque f : Nat"],
        "native": ["  native_decide", "  decide +kernel; bv_decide"],
        "partial": ["partial def loop : Nat := loop", "private partial def loop : Nat := loop"],
        "semantics-class": ["class FooSemantics [GoSemanticsFunctions] : Prop where",
                            "noncomputable instance : GoLocalContext := ⟨f⟩",
                            "instance foo [GooseExts] : go.Float64Semantics := ⟨⟩"],
    }
    must_not = {
        "step-rule": ["  intro _ _ _ h; exact h.isGoStep_det_internal",
                      "  float64Encodes (float64Add v1 v2) f"],
        "axiom": ["  -- the axiom of choice", "#print axioms foo"],
        "semantics-class": ["noncomputable instance runeStruct.zero_val [GooseExts] : ZeroVal runeStruct :=",
                            "instance [GoSemanticsFunctions] (T : go.GoType) : Foo T := ⟨⟩"],
    }
    bad = []
    for name, lines in must.items():
        for ln in lines:
            if name not in [n for n, _ in signals_in(ln)]:
                bad.append(f"missed `{name}`: {ln!r}")
    for name, lines in must_not.items():
        for ln in lines:
            if name in [n for n, _ in signals_in(ln)]:
                bad.append(f"spurious `{name}`: {ln!r}")
    # a continuation line of a multi-line relational rule belongs to that rule
    src = "\n".join([
        "class Float64Semantics [GoSemanticsFunctions] : Prop where",
        "  /-- a docstring mentioning is_go_step_pure",
        "  over two lines -/",
        "  le_float64 (v1 v2 : w64) : ⟦GoOp GoLe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Leb v1 v2)",
        "  plus_float64 {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :",
        "    is_go_step_pure (GoOp GoPlus t) glv((#v1, #v2)) =",
        "      fun (e : Expr) => ∃ f, e = #f ∧ float64Encodes (float64Add v1 v2) f",
        "  zero_float64 : ZeroVal w64",
        "",
        "def helper (x : w64) : w64 := x",
    ])
    ids, stmts, is_code = decl_statements(src)
    if not (ids[4] == ids[5] == ids[6] and re.search(STEP_RULE, stmts[ids[6]][1])):
        bad.append("decl_statements: the body of `plus_float64` is not in its rule")
    if ids[7] == ids[6] or re.search(STEP_RULE, stmts[ids[7]][1]):
        bad.append("decl_statements: `zero_float64` is attributed to a step rule")
    if re.search(STEP_RULE, stmts[ids[9]][1]) or "docstring" in stmts[ids[3]][1] or is_code[2]:
        bad.append("decl_statements: comment text or a top-level def counted as a step rule")
    for b in bad:
        print("FAIL " + b)
    print(f"trusted-delta self-test: {'FAILED' if bad else 'ok'}")
    return 1 if bad else 0

# --------------------------------------------------------------- main
def main(argv):
    if "--self-test" in argv:
        return self_test()
    full = "--full" in argv
    nodiff = "--no-diff" in argv
    check = "--check" in argv
    argv = [a for a in argv if not a.startswith("--")]
    desc, diff_args, rev_new, rev_old = resolve_target(argv)
    files = parse_diff(diff_args)
    if not files:
        print(f"trusted-delta: {desc}: no changes")
        return 0

    tiered = {0: [], 1: [], 2: [], 3: []}
    for p in sorted(files):
        t, kind = tier_of(p)
        tiered[t].append((p, kind))

    print(f"# Trust delta: {desc}\n")
    print("## Files by tier\n")
    for t in range(4):
        if not tiered[t]:
            continue
        label = {0: "tier 0 (TRUSTED)", 1: "tier 1 (generated)", 2: "tier 2 (logic/libraries)", 3: "tier 3 (proofs, docs, tooling)"}[t]
        print(f"### {label}")
        for p, kind in tiered[t]:
            f = files[p]
            plus = sum(1 for _, s, _, _ in f["lines"] if s == "+")
            minus = sum(1 for _, s, _, _ in f["lines"] if s == "-")
            print(f"- [{f['status']}] {p}  ({kind}; +{plus} -{minus})")
        print()

    # signals
    print("## Signals in changed lines\n")
    nsig = 0
    for t in range(4):
        for p, kind in tiered[t]:
            hits = []
            for (ln, s, text, prose), oln in zip(files[p]["lines"], files[p]["old"]):
                if prose:
                    continue
                for name, why in signals_in(text):
                    # a removed line is located by its line number in the old file
                    hits.append((ln if s == "+" else oln, s, name, text.strip()))
            if t == 0:
                hits += step_rule_context_hits(p, files[p], rev_old, rev_new)
                hits.sort(key=lambda h: (h[0], h[1] == "+"))
            if not hits:
                continue
            nsig += len(hits)
            print(f"### {p}  (tier {t}, {kind})")
            seen, per_name = set(), {}
            for ln, s, name, text in hits:
                key = (ln, s, name)
                if key in seen:
                    continue
                seen.add(key)
                # outside tier 0 (e.g. a goose regeneration), list a few of each signal
                per_name[name] = per_name.get(name, 0) + 1
                if t > 0 and per_name[name] > COLLAPSE:
                    continue
                loc = f"{p}:{ln}" if s == "+" else f"{p}:{ln} (removed; old line)"
                print(f"- `{name}` {loc}: `{text[:200]}`")
            for name, n in per_name.items():
                if t > 0 and n > COLLAPSE:
                    print(f"- `{name}`: ... and {n - COLLAPSE} more lines in this file")
            print()
    if nsig == 0:
        print("(none)\n")
    print("Signal legend:")
    for name, _, why in SIGNALS:
        print(f"- `{name}`: {why}")
    print()

    # goose configuration deltas
    cfg = [(p, kind) for p, kind in tiered[0] if kind == "goose-config"]
    if cfg:
        print("## goose configuration (trusted / translated / axiomatized / skipped)\n")
        for p, _ in cfg:
            lists, reasons, old_reasons = toml_lists(p, rev_old, rev_new)
            for key, added, removed in lists:
                print(f"- {p} `{key}`: added {added or '[]'}, removed {removed or '[]'}")
                if key == "skip":
                    pkg = config_pkg(p)
                    for name in added:
                        print(f"  - skipped `{pkg}.{name}`: reason: \"{reasons.get(name, '')}\"")
                        print("    The reason must show that Go's initializer terminates, cannot panic "
                              "and has no effect beyond the variable; read its callees (an effect "
                              "on another variable or package, a registration, is not skippable).")
                        if name == "_":
                            print("    (`_`: every blank `var _` of the package; the translation's "
                                  "`skipped'` lists each one with its source)")
                            continue
                        src = go_source(f"{pkg}.{name}", unexported=True)
                        if src:
                            lines = src.rstrip().split("\n")
                            if len(lines) > 40:
                                lines = lines[:40] + [f"... ({len(lines) - 40} more lines)"]
                            print(f"    Go source (`go doc -u -src {pkg}.{name}`):\n")
                            print("```go\n" + "\n".join(lines) + "\n```\n")
                        else:
                            print(f"    (`go doc -u -src {pkg}.{name}` found nothing: read the initializer yourself)")
                    for name in removed:
                        print(f"  - no longer skipped `{name}` (was: \"{old_reasons.get(name, '')}\")")
                if key == "trusted":
                    pkg = os.path.relpath(p, "Perennial/Code")[: -len(".toml")]
                    for name in added:
                        print(f"  - R2: `{name}` must be justified by a goose run on the real "
                              f"source that fails on something irreducible (not a missing goose "
                              f"feature or semantics rule): move it to `translate` in a copy of the "
                              f"configuration and run `goose -configdir <copy> -dir goose {pkg}` "
                              f"(SKILL.md, step 4)")
        print("\nA declaration that is neither translated nor trusted is axiomatized "
              "(name and type only). A `!pattern` in `translate` with the same name in "
              "`trusted` replaces goose's translation by a hand-written model: ask why "
              "the real translation is not used.\n")

    # trusted models vs Go source
    tm = [p for p, kind in tiered[0] if kind == "trusted-model"]
    if tm:
        print("## Trusted models vs the Go source\n")
        for p in tm:
            for n, gosym, block in trusted_impls(p, files, rev_new):
                print(f"### {p}: `{n}.impl`\n")
                if block:
                    print("Go code quoted by the model's docstring (what the model claims to be):\n")
                    print("```go\n" + block.rstrip() + "\n```\n")
                else:
                    print("(the docstring quotes no Go code: the model must be read as GooseLang)\n")
                src = go_source(gosym)
                if src:
                    print(f"Real Go source (`go doc -src {gosym}`):\n")
                    print("```go\n" + src.rstrip() + "\n```\n")
                else:
                    print(f"(`go doc -src {gosym}` found nothing: fetch the source yourself)\n")
                if block and src and re.sub(r"\s", "", block) not in re.sub(r"\s", "", src):
                    print("NOTE: the quoted Go differs from the real source. Every difference is a "
                          "modelling decision to justify (or a workaround for a semantics gap: "
                          "rule R2 of the skill).\n")

    # diffs
    if not nodiff:
        print("## Diffs\n")
        for t in range(4):
            if t > 0 and not full:
                break
            for p, kind in tiered[t]:
                print(f"### {p}  (tier {t}, {kind})\n")
                print("```diff\n" + files[p]["raw"] + "\n```\n")
        if not full and any(tiered[t] for t in (1, 2, 3)):
            print("(tiers 1-3 omitted; `--full` prints them, or `git diff` the files above)\n")

    if check and tiered[0]:
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
