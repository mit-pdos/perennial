#!/usr/bin/env python3
"""Trust delta of a change: which trusted files it touches and what it adds to
the trusted base. Input to the `review-trusted` skill
(.agents/skills/review-trusted/SKILL.md); it does not judge, it reports.

Usage: etc/trusted-delta.py [TARGET] [--full] [--no-diff] [--check]
       etc/trusted-delta.py --self-test
       etc/trusted-delta.py --witness-gate A..B | --witness-paths A..B

  TARGET     a commit (reviews that commit: COMMIT^..COMMIT), a range A..B, or
             nothing: the working tree against the merge base with origin/lean
             (committed and uncommitted work of the current branch)
  --full     print the diff of every changed file, not only the trusted ones
  --no-diff  print only the summary and the signal lines
  --check    exit 1 if the change touches the trusted base (tier 0) at all,
             or changes a generated `skipped'` entry, for use in hooks
  --self-test  check the signal patterns (and the witness gate) on built-in examples and exit
  --witness-gate A..B   the semantics-witness gate of `etc/land.sh push`: exit 1 if the
             range adds to the model of Go (a gated signal on an added tier-0 line: see
             GATE_SIGNALS) and its commits lack a valid `Semantics-Witness:` and `Real-use:`
             trailer (criterion 1 of .agents/skills/review-trusted/CRITERIA.md)
  --witness-paths A..B  print the range's valid witness paths (`<kind> <path>`) for land.sh

Skipped package variables: for every variable a goose config newly lists in a
`[[skip]]` entry (or `skip = [...]`), it prints the reason and the variable's
Go source (`go doc -u -src`). Every added, removed or changed entry of a
generated `skipped'` list (`Perennial/Code/<pkg>.lean`: a Go upgrade that adds,
moves or changes a skipped variable, or a changed reason) is a change to the
trusted base too: it is listed in its own section, and counts for `--check`.

Go model overlays: for every changed goose config with a `[model]` table, and every
config whose `[model].dir` holds a changed model file (configs are found at both
revisions, in Perennial/Code and goose/testdata; a non-test `.go` file of such a
dir is tier 0, `go-model-overlay`, wherever it sits), it prints the table before
and after; for every replaced declaration that is new or whose model changed, the
model's Go source (with its doc comment, and a NOTE if that does not start with
`MODEL:`) next to the real one (`go doc -u -src`; not for `init.N`, which go doc
cannot name); the unchanged replaced names; and every addition, marking the
primitive stubs (additions in `trusted`) and whether an added method matches
`added_methods`.

Tiers (see the skill): 0 = trusted (semantics, translator, trusted models,
goose configuration, Go model overlays); 1 = generated (trusted through goose; hand edits are
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
import os, re, shutil, subprocess, sys, tomllib

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

# --------------------------------------------------------------- tiers
TIER0 = [
    ("semantics", r"^Perennial/GooseLang/(Lang|BoundedLang|Adequacy|AdequacyAlong|Threads|Receipts|Locations|Ext|CrashLang|CrashAdequacy|DistLang|DistAdequacy|InitAdequacy)\.lean$"),
    ("semantics", r"^Perennial/GooseLang/Ext/"),
    ("semantics", r"^Perennial/Golang/Defn(/|\.lean$)"),
    ("semantics", r"^Perennial/GrovePrelude\.lean$"),
    ("translator", r"^goose/.*\.go$"),
    ("translator-gold", r"^goose/testdata/.*\.gold\.lean$"),
    ("go-model", r"^goose/model/"),
    ("trusted-model", r"^Perennial/TrustedCode/"),
    ("goose-config", r"^Perennial/Code/.*\.toml$"),
    # the configs of goose's tests: their `[model]` tables and trust lists shape the gold files
    ("test-config", r"^goose/testdata/.*\.toml$"),
]
# Besides these, every non-test `.go` file of a goose config's `[model].dir` is tier 0
# (`go-model-overlay`), wherever it sits: see `model_owners`.
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
    ("model-table", r"^\s*\[model\]", "goose configuration: a Go model overlay (model Go replaces or adds to the real package; R12)"),
    ("model-replaces", r"^\s*(replaces|added_methods)\s*=\s*\[",
     "goose configuration: which real declarations a Go model replaces, or which methods it may add to real types (R12)"),
    ("gomodel-replace", r"//gomodel:replace\b", "a Go model `init` that replaces a real `init.N` (R12)"),
    ("gomodel-choice", r"\bgomodel\.(Choose|ChooseUint64|Stuck)\s*\(",
     "a choice or stuck point in a Go model: needs a reason (review-trusted)"),
]

# Outside tier 0, at most this many lines of each signal are listed per file.
COLLAPSE = 8

def is_prose(path, text):
    """Comment, markdown or toml-comment line: signals there are words, not code."""
    if path.endswith(".md"):
        return True
    t = text.lstrip()
    if t.startswith("//gomodel:"):
        return False  # a Go model directive: code, whatever counts as prose

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
GO = shutil.which("go") or "/usr/local/go/bin/go"

def go_source(symbol, unexported=False, cwd=ROOT):
    """`go doc -src strings.Split` (`-u` also for unexported names), run in `cwd` (whose
    module must provide the package); '' if the toolchain cannot find it."""
    # read-only: never let `go doc` rewrite go.sum / go.work.sum
    env = dict(os.environ, GOFLAGS="-mod=readonly", GOWORK="off")
    try:
        r = subprocess.run([GO, "doc"] + (["-u"] if unexported else []) + ["-src", symbol], cwd=cwd, capture_output=True,
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
    pkg = config_pkg("Perennial/Code/" + re.sub(r"^Perennial/TrustedCode/|\.lean$", "", path) + ".toml", rev)
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

PKG_ID = re.compile(r'^namespace pkg_id\nnoncomputable def \S+ : GoString := go!"([^"]+)"', re.M)

def config_pkg(path, rev=None):
    """The Go package of a goose config Perennial/Code/<pkg>.toml: the Go path its translation
    (Perennial/Code/<pkg>.lean, at `rev`, else at HEAD) declares as its `pkg_id`. The file name
    is no guide: goose maps both `.` and `-` to `_` (github_com/mit_pdos/...). Without a
    translation, the file name with `_` read as `/`-separated path components (right for the
    standard library)."""
    if path.startswith("goose/testdata/"):
        return testdata_pkg(path)[0]
    lean = path[: -len(".toml")] + ".lean"
    for r in ([rev] if rev is not None else []) + ["HEAD"]:
        m = PKG_ID.search(file_at(r, lean))
        if m:
            return m.group(1)
    m = PKG_ID.search(file_at(None, lean))
    return m.group(1) if m else os.path.relpath(path, "Perennial/Code")[: -len(".toml")]

def testdata_pkg(path):
    """(import path, directory) of the package of a goose test config
    goose/testdata/<group>/<pkg>/<encoded import path>.toml: the directory is the nearest
    ancestor of the config holding a `.go` file, its import path the enclosing module's path
    plus the directory (read in the working tree). (None, None) if not found."""
    d = os.path.dirname(path)
    while d.startswith("goose/testdata/"):
        try:
            if any(n.endswith(".go") for n in os.listdir(os.path.join(ROOT, d))):
                break
        except OSError:
            pass
        d = os.path.dirname(d)
    else:
        return None, None
    m = d
    while m.startswith("goose/"):
        mod = re.search(r"^module\s+(\S+)", file_at(None, m + "/go.mod"), re.M)
        if mod:
            rel = os.path.relpath(d, m)
            return (mod.group(1) + ("" if rel == "." else "/" + rel)), d
        m = os.path.dirname(m)
    return None, d

def config_go_dir(path):
    """Where `go doc` finds the package of a goose config: the repository root, or for a
    test config the test package's own module."""
    if path.startswith("goose/testdata/"):
        d = testdata_pkg(path)[1]
        return os.path.join(ROOT, d) if d else ROOT
    return ROOT

# --------------------------------------------------------------- Go model overlays
def model_table(text):
    """The `[model]` table of a goose config: {"dir", "replaces", "added_methods"}, or
    None."""
    m = parse_config(text).get("model") if text else None
    if not isinstance(m, dict):
        return None
    return {"dir": str(m.get("dir", "")).strip("/"),
            "replaces": [str(x) for x in m.get("replaces", [])] if "replaces" in m else None,
            "added_methods": [str(x) for x in m.get("added_methods", [])]}

def pattern_contains(patterns, name):
    """goose's pattern sets (declfilter): `*` matches anything, `!p` removes, the last
    matching pattern decides."""
    b = False
    for p in patterns:
        neg = p.startswith("!")
        rx = "^" + ".*".join(re.escape(x) for x in p[1 if neg else 0:].split("*")) + "$"
        if re.match(rx, name):
            b = not neg
    return b

def model_owners(rev):
    """{config path: its `[model]` table} for every goose config at `rev` (None: the
    working tree) that has one: Perennial/Code/**.toml and goose/testdata/**.toml."""
    args = ["grep", "-l", "-E", r"^\s*\[model\]"] + (["--untracked"] if rev is None else [rev])
    out = git(*args, "--", "Perennial/Code/*.toml", "goose/testdata/*.toml", check=False)
    res = {}
    for line in out.split("\n"):
        if not line:
            continue
        p = line.split(":", 1)[1] if rev is not None else line
        t = model_table(file_at(rev, p))
        if t:
            res[p] = t
    return res

def tier_files(files, rev_old, rev_new):
    """-> ({tier: [(path, kind)]}, model_owner_of): the changed files by tier, a non-test
    `.go` file of a `[model].dir` (at either revision) counting as tier 0 `go-model-overlay`;
    model_owner_of(path) is the set of configs whose `[model].dir` holds `path`."""
    owners_new, owners_old = model_owners(rev_new), model_owners(rev_old)
    model_dirs = {}
    for owners in (owners_old, owners_new):
        for c, t in owners.items():
            if t["dir"]:
                model_dirs.setdefault(t["dir"], set()).add(c)

    def model_owner_of(p):
        if p.endswith(".go") and not p.endswith("_test.go"):
            return model_dirs.get(os.path.dirname(p), set())
        return set()

    tiered = {0: [], 1: [], 2: [], 3: []}
    for p in sorted(files):
        t, kind = tier_of(p)
        if model_owner_of(p):
            t, kind = 0, "go-model-overlay"
        tiered[t].append((p, kind))
    return tiered, model_owner_of

def model_files(rev, d):
    """The model files of a `[model].dir` at `rev`: its non-test `.go` files."""
    if not d:
        return []
    if rev is None:
        try:
            names = sorted(os.listdir(os.path.join(ROOT, d)))
        except OSError:
            return []
        paths = [f"{d}/{n}" for n in names]
    else:
        paths = git("ls-tree", "--name-only", rev, "--", d + "/", check=False).split()
    return [p for p in paths if p.endswith(".go") and not p.endswith("_test.go")]

def go_code_lines(src):
    """Per line of Go source: (code, bracket depth at its start, at its end), where code is
    the line without comments and with string and rune contents blanked out."""
    out, state, depth = [], None, 0
    for line in src.split("\n"):
        d0, code, i, n = depth, [], 0, len(line)
        while i < n:
            if state == "block":
                j = line.find("*/", i)
                if j < 0:
                    break
                state, i = None, j + 2
                code.append(" ")
                continue
            if state == "raw":
                j = line.find("`", i)
                if j < 0:
                    break
                state, i = None, j + 1
                code.append("`")
                continue
            c = line[i]
            if line.startswith("//", i):
                break
            if line.startswith("/*", i):
                state, i = "block", i + 2
                continue
            if c == "`":
                state, i = "raw", i + 1
                code.append("`")
                continue
            if c in "\"'":
                j = i + 1
                while j < n and line[j] != c:
                    j += 2 if line[j] == "\\" else 1
                code.append(c + c)
                i = j + 1
                continue
            if c in "({[":
                depth += 1
            elif c in ")}]":
                depth -= 1
            code.append(c)
            i += 1
        out.append(("".join(code).rstrip(), d0, depth))
    return out

GO_REPLACE = re.compile(r'^\s*//gomodel:replace\s+(init\.\d+)\s*(.*)$')

def go_decls(src):
    """The top-level declarations of a Go file, one per function, method, and type, var or
    const spec (a spec of a `var (...)` group is its own declaration), each with its doc
    comment: [{"names", "kind", "line" (1-based, of the doc comment if any), "text",
    "marker" (an `init`'s `//gomodel:replace` quote)}]. A method is named `T.m`; an
    `init` marked `//gomodel:replace init.N` is named `init.N`, an unmarked one `init#K`
    (the K-th unmarked one of the file). Brace matching on the source with comments and
    strings blanked out: enough for gofmt-formatted files."""
    lines, cl = src.split("\n"), go_code_lines(src)
    decls, unmarked = [], 0

    def doc_start(i):
        while i > 0 and lines[i - 1].strip() and not cl[i - 1][0].strip():
            i -= 1
        return i

    def add(kind, names, i, k):
        nonlocal unmarked
        ds = doc_start(i)
        text = "\n".join(lines[ds:k + 1])
        marker = None
        if names == ["init"] and kind == "func":
            for l in lines[ds:i]:
                m = GO_REPLACE.match(l)
                if m:
                    names, marker = [m.group(1)], m.group(2)
            if marker is None:
                unmarked += 1
                names = [f"init#{unmarked}"]
        decls.append({"names": names, "kind": kind, "line": ds + 1, "text": text, "marker": marker})

    def end_of(k, level):
        while k < len(lines) - 1 and cl[k][2] > level:
            k += 1
        return k

    i = 0
    while i < len(lines):
        code, d0, _ = cl[i]
        m = re.match(r"(func|type|var|const|import)\b", code) if d0 == 0 else None
        if not m:
            i += 1
            continue
        kw = m.group(1)
        if kw != "func" and re.match(kw + r"\s*\($", code):  # a group: one declaration per spec
            j = i + 1
            while j < len(lines):
                c, e0, _ = cl[j]
                if e0 <= 1 and c.strip().startswith(")"):
                    break
                if e0 == 1 and c.strip():
                    k = end_of(j, 1)
                    nm = re.match(r"\s*(\w+(?:\s*,\s*\w+)*)", c)
                    if kw != "import" and nm:
                        add(kw, [x.strip() for x in nm.group(1).split(",")], j, k)
                    j = k + 1
                else:
                    j += 1
            i = j + 1
            continue
        k = end_of(i, 0)
        if kw == "func":
            mm = re.match(r"func\s*\(([^)]*)\)\s*(\w+)", code)
            if mm:
                recv = re.search(r"(\w+)\s*(\[.*\])?\s*$", mm.group(1))
                add("method", [f"{recv.group(1) if recv else '?'}.{mm.group(2)}"], i, k)
            else:
                mf = re.match(r"func\s+(\w+)", code)
                add("func", [mf.group(1) if mf else "?"], i, k)
        elif kw != "import":
            nm = re.match(kw + r"\s+(\w+(?:\s*,\s*\w+)*)", code)
            if nm:
                add(kw, [x.strip() for x in nm.group(1).split(",")], i, k)
        i = k + 1
    return decls

def model_decls(rev, d):
    """{name: (model file, declaration)} of the model files of `d` at `rev`."""
    out = {}
    for p in model_files(rev, d):
        for dc in go_decls(file_at(rev, p)):
            for n in dc["names"]:
                if n != "_":
                    out[n] = (p, dc)
    return out

def doc_starts_with_model(text):
    """Whether a declaration's doc comment (directives aside) starts with `MODEL:`."""
    for l in text.split("\n"):
        t = l.strip()
        if re.match(r"//(go|gomodel|line)\b", t):
            continue
        return bool(re.match(r"//\s*MODEL:", t))
    return False

def clip(text, n):
    lines = text.rstrip().split("\n")
    return "\n".join(lines[:n] + ([f"... ({len(lines) - n} more lines)"] if len(lines) > n else []))

def fmt_model(t):
    if t is None:
        return "none"
    r = "(missing: a config error)" if t["replaces"] is None else t["replaces"]
    return f"dir = {t['dir']!r}, replaces = {r}, added_methods = {t['added_methods']}"

def report_model(cpath, rev_old, rev_new, changed_paths):
    """The `[model]` section of one goose config: the table before and after; for every
    replaced declaration that is new or changed, the model's Go source next to the real
    one; every addition, and which ones are primitive stubs (also in `trusted`); and the
    model declarations the config's `translate` excludes, which goose translates
    names-only."""
    old_txt, new_txt = file_at(rev_old, cpath), file_at(rev_new, cpath)
    old, new = model_table(old_txt), model_table(new_txt)
    pkg, gocwd = config_pkg(cpath, rev_new), config_go_dir(cpath)
    print(f"### {cpath}  (package `{pkg}`)\n")
    if old == new:
        print(f"- `[model]` (unchanged): {fmt_model(new)}")
    else:
        print(f"- `[model]` before: {fmt_model(old)}")
        print(f"- `[model]` after:  {fmt_model(new)}")
    if new is None:
        print("- the model overlay is removed: every real declaration is goose's translation "
              "(or trusted/axiomatized by the config) again\n")
        return
    lists = goose_lists(new_txt)
    trusted = lists.get("trusted", [])
    translate = lists.get("translate") or ["*"]
    nd = model_decls(rev_new, new["dir"])
    od = model_decls(rev_old, old["dir"]) if old else {}
    files = model_files(rev_new, new["dir"])
    touched = [p for p in files if p in changed_paths]
    print(f"- model files: {', '.join(files) or '(none: a config error)'}"
          + (f"; changed: {', '.join(touched)}" if touched else ""))
    whole = new["replaces"] == ["*"]
    rep_new = set(new["replaces"] or [])
    rep_old = set((old or {}).get("replaces") or [])
    if whole:
        print("- whole-package model (`replaces = [\"*\"]`): every real file is dropped; every "
              "model declaration that is not a primitive stub carries the R12 claim against the "
              "real declaration of the same name, if any")
    for n in sorted(rep_old - rep_new - {"*"}):
        print(f"- no longer replaced: `{n}` (the real declaration is back)")
    stubs = lambda n: pattern_contains(trusted, n)
    # translate governs model declarations as real ones: excluded and not trusted is names-only
    names_only = lambda n: not pattern_contains(translate, n) and not stubs(n)
    if whole:
        claimed = [n for n in nd if not stubs(n) and not names_only(n)]
    else:
        claimed = sorted(rep_new)
    status = lambda n: ("new" if n not in od or (not whole and n not in rep_old) else
                        "changed" if od[n][1]["text"] != nd[n][1]["text"] else None)
    shown, same = [], []
    for n in claimed:
        if n not in nd:
            print(f"- replaced `{n}`: the model declares no `{n}` (a config error)")
            continue
        (shown if status(n) else same).append(n)
    print()
    for n in shown:
        p, dc = nd[n]
        print(f"#### `{pkg}.{n}` ({status(n)})\n")
        print(f"Model ({p}:{dc['line']}):\n")
        print("```go\n" + clip(dc["text"], 80) + "\n```\n")
        if not doc_starts_with_model(dc["text"]):
            print("NOTE: the doc comment does not start with `MODEL:` (R12).\n")
        if n.startswith("init#"):
            print("(an unmarked model `init`: it runs after the real package's inits)\n")
            continue
        if n.startswith("init."):
            print(f"(`go doc` cannot show `{n}`, the real package's init of that number in goose's "
                  f"numbering: read it in the real source. The marker quotes its first body "
                  f"line: {dc['marker'] or '(none)'})\n")
            continue
        real = go_source(f"{pkg}.{n}", unexported=True, cwd=gocwd)
        if real:
            print(f"Real (`go doc -u -src {pkg}.{n}`):\n")
            print("```go\n" + clip(real, 80) + "\n```\n")
        elif whole:
            print("(no real declaration found by `go doc`: a model-only helper, or an added package)\n")
        else:
            print(f"(`go doc -u -src {pkg}.{n}` found nothing: fetch the real source yourself)\n")
    if same:
        print("Replaced, unchanged: " + ", ".join(f"`{n}`" for n in same) + "\n")
    nonly = sorted(n for n in nd if names_only(n))
    if nonly:
        print("Names-only (excluded by `translate`, not trusted: the declaration is translated "
              "without its body, so only its name and type are claimed): " + ", ".join(f"`{n}`" for n in nonly) + "\n")
    adds = [n for n in nd if n not in rep_new and not (whole and not stubs(n)) and not names_only(n)]
    if adds:
        print("Additions (no claim of their own; a primitive stub carries the TrustedCode claim, "
              "R2; an added method must match `added_methods`):\n")
        for n in adds:
            p, dc = nd[n]
            tags = []
            if stubs(n):
                tags.append("PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)")
            if dc["kind"] == "method":
                tags.append("matches `added_methods`" if pattern_contains(new["added_methods"], n)
                            else "a method: of a model-only type, or a config error")
            if n.startswith("init#"):
                tags.append("unmarked `init`: runs after the real ones")
            st = "new" if n not in od else ("changed" if od[n][1]["text"] != dc["text"] else "unchanged")
            print(f"- `{n}` ({dc['kind']}, {p}:{dc['line']}, {st})" + ("".join(f"; {t}" for t in tags)))
        print()
    gone = [n for n in od if n not in nd]
    if gone:
        print("Model declarations removed: " + ", ".join(f"`{n}`" for n in sorted(gone)) + "\n")

# --------------------------------------------------------------- skipped' entries
LEAN_STR = re.compile(r'"((?:[^"\\]|\\.)*)"')

def lean_unescape(s):
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            if n == "n":
                out.append("\n"); i += 2
            elif n == "t":
                out.append("\t"); i += 2
            elif n == "r":
                out.append("\r"); i += 2
            elif n == "x":
                out.append(chr(int(s[i + 2:i + 4], 16))); i += 4
            elif n == "u":
                j = s.index("}", i)
                out.append(chr(int(s[i + 3:j], 16))); i = j + 1
            else:
                out.append(n); i += 2
        else:
            out.append(c); i += 1
    return "".join(out)

def skipped_entries(text):
    """The entries of a generated `skipped' : List go.SkippedVar := [⟨"name", "reason", "decl"⟩,
    ...]`: {name: (fields after the name)}. Strings are scanned as Lean literals, so a `⟩` or
    `]` inside one does not end an entry."""
    m = re.search(r"def skipped' : List go\.SkippedVar := \[", text)
    if not m:
        return {}
    out, i, cur = {}, m.end(), None
    while i < len(text):
        c = text[i]
        if c == '"':
            sm = LEAN_STR.match(text, i)
            if cur is not None:
                cur.append(lean_unescape(sm.group(1)))
            i = sm.end()
            continue
        if c == "⟨":
            cur = []
        elif c == "⟩" and cur is not None:
            if cur:
                out[cur[0]] = tuple(cur[1:])
            cur = None
        elif c == "]" and cur is None:
            break
        i += 1
    return out

def skipped_delta(path, rev_old, rev_new):
    """Added, removed and changed `skipped'` entries of a generated file:
    [(sign '+'/'-'/'~', name, old fields, new fields)]."""
    old, new = skipped_entries(file_at(rev_old, path)), skipped_entries(file_at(rev_new, path))
    out = []
    for n in new:
        if n not in old:
            out.append(("+", n, None, new[n]))
        elif old[n] != new[n]:
            out.append(("~", n, old[n], new[n]))
    for n in old:
        if n not in new:
            out.append(("-", n, old[n], None))
    return out

# --------------------------------------------------------------- witness gate
# `etc/land.sh push` refuses a change that adds to the semantics unless its commits
# carry a witness (criterion 1 of .agents/skills/review-trusted/CRITERIA.md):
#   Semantics-Witness: <path>    a goose example or Lean test exercising the addition
#   Real-use: <repo>:<package>.<function>    a real translated function that needs it
# or, for a change that only removes trust or makes the model stuck in more places,
#   Semantics-Witness: none (narrowing: <reason>)
#
# The gate fires on these signals, on ADDED (or changed) code lines of tier-0 files of
# the kinds below; a pure deletion never fires it.
GATE_SIGNALS = {
    "step-rule",        # a new or changed step rule or unfolding (incl. a changed line inside one)
    "semantics-class",  # a new semantics class or instance
    "new-instruction",  # a new constructor of `inductive GoInstruction`
    "assume",           # a model assumption: removes executions
    "angelic",          # an angelic exit: removes executions
    "axiom",            # trusted outright (also in tier 2, where review grades it BLOCK)
    "extension",        # an extension's semantics: new primitive operations
    "trusted-impl",     # a hand-written GooseLang model of Go code
    "model-table",      # a Go model overlay
    "model-replaces",   # real declarations a Go model replaces / methods it adds
    "gomodel-replace",  # a Go model of an `init.N`
    "gomodel-choice",   # a choice or stuck point of a Go model
}
# Tier-0 kinds the gate looks at: the model of Go. The translator (`goose/*.go`), its gold
# files and test configs are not gated: a translator change already needs its gold test.
GATE_KINDS = {"semantics", "trusted-model", "go-model", "goose-config", "go-model-overlay"}
# Signals that only ever add trust: the narrowing escape is refused when one of them fires.
NOT_NARROWING = {"assume", "angelic", "axiom", "new-instruction", "model-table"}

WITNESS_KEY, REAL_USE_KEY = "Semantics-Witness", "Real-use"
NARROWING_RX = re.compile(r"^none\s*\(narrowing:\s*(\S.*)\)$")
REAL_USE_RX = re.compile(r"^[^\s:]+:\S+\.[^\s.]+$")

def witness_location(path):
    """Where a witness path is exercised by `etc/land.sh` (None: nowhere, refused):
    'go-example' (goose/testdata/examples/**.go: translated and gold-checked by
    `go test ./goose/...`; examples/semantics also run in Go), or 'lean' (a Lean test or
    proof under Perennial/ProgramLogic/*Test.lean or Perennial/Proof/**, built by lake)."""
    if re.match(r"^goose/testdata/examples/.+\.go$", path) and not path.endswith("_test.go"):
        return "go-example"
    if re.match(r"^Perennial/ProgramLogic/\w+Test\.lean$", path) or \
            re.match(r"^Perennial/Proof/.+\.lean$", path):
        return "lean"
    return None

def new_instruction_hits(content, added_lns):
    """Added lines (1-based numbers) of `content` that are constructors of
    `inductive GoInstruction`. -> [(ln, text)]"""
    if "inductive GoInstruction" not in content:
        return []
    _, _, is_code = decl_statements(content)
    lines = content.split("\n")
    inside, in_instr = False, []
    for i, line in enumerate(lines):
        if is_code[i] and line[:1].strip():  # a code line at indentation 0 starts a declaration
            inside = bool(re.match(MODS + r"inductive\s+GoInstruction\b", line))
        in_instr.append(inside)
    out = []
    for ln in added_lns:
        i = ln - 1
        if 0 <= i < len(lines) and is_code[i] and in_instr[i] and re.match(r"^\s*\|\s*[A-Za-z_]", lines[i]):
            out.append((ln, lines[i].strip()))
    return out

def gate_triggers(files, rev_old, rev_new):
    """The changed lines that make a change need a witness. -> [(path, ln, signal, text)]"""
    tiered, _ = tier_files(files, rev_old, rev_new)
    out = []
    for t in (0, 1, 2):
        for p, kind in tiered[t]:
            gated = t == 0 and kind in GATE_KINDS
            f = files[p]
            # in Lean, whether a line is code is read off the whole new file (a line inside a
            # docstring opened outside the hunk is prose; a constructor `| C` is code)
            is_code = decl_statements(file_at(rev_new, p))[2] if p.endswith(".lean") else None
            def code(ln, prose):
                return (0 < ln <= len(is_code) and is_code[ln - 1]) if is_code is not None else not prose
            for ln, s, text, prose in f["lines"]:
                if s != "+" or not code(ln, prose):
                    continue
                for name, _ in signals_in(text):
                    if (gated and name in GATE_SIGNALS) or name == "axiom":
                        out.append((p, ln, name, text.strip()))
            if not gated:
                continue
            out += [(p, ln, name, text) for ln, s, name, text in step_rule_context_hits(p, f, rev_old, rev_new)
                    if s == "+"]
            if p.endswith(".lean"):
                added = [ln for ln, s, _, prose in f["lines"] if s == "+" and code(ln, prose)]
                out += [(p, ln, "new-instruction", text)
                        for ln, text in new_instruction_hits(file_at(rev_new, p), added)]
    return sorted(set(out))

def commit_trailers(rng, key):
    """The values of trailer `key` on the commits of `rng` (A..B), in log order."""
    out = git("log", f"--format=%(trailers:key={key},valueonly,unfold,separator=%x1e)%x1f", rng)
    vals = []
    for rec in out.split("\x1f"):
        vals += [v.strip() for v in rec.split("\x1e") if v.strip()]
    return vals

def check_witness(triggers, witnesses, real_uses, exists):
    """The gate's verdict on a change. `exists(path)`: whether the path is in the change's
    head revision. The gate passes with one valid witness and one well-formed real use, or,
    when the change adds nothing in NOT_NARROWING, with a narrowing witness; a trailer that
    is not valid is reported but does not refuse when another one satisfies the gate.
    -> (problems: the gate refuses if non-empty, warnings)"""
    if not triggers:
        return [], []
    fired = {name for _, _, name, _ in triggers}
    if not witnesses:
        return [f"no `{WITNESS_KEY}:` trailer on the branch's commits"], []
    bad, real, narrowing = [], [], []
    for w in witnesses:
        if NARROWING_RX.match(w):
            narrowing.append(w)
        elif w.startswith("none"):
            bad.append(f"`{WITNESS_KEY}: {w}`: the only accepted `none` is `none (narrowing: <reason>)`")
        elif not exists(w):
            bad.append(f"`{WITNESS_KEY}: {w}`: no such file in the branch's head")
        elif witness_location(w) is None:
            bad.append(f"`{WITNESS_KEY}: {w}`: not a regression test land.sh runs (a goose example "
                       f"`goose/testdata/examples/**.go`, `Perennial/ProgramLogic/*Test.lean` or "
                       f"`Perennial/Proof/**.lean`)")
        else:
            real.append(w)
    good_uses = [r for r in real_uses if REAL_USE_RX.match(r)]
    bad += [f"`{REAL_USE_KEY}: {r}`: not of the form `<repo>:<package>.<function>`"
            for r in real_uses if not REAL_USE_RX.match(r)]
    if real and good_uses:
        return [], bad
    probs = []
    if real:
        probs.append(f"no well-formed `{REAL_USE_KEY}: <repo>:<package>.<function>` trailer")
    elif narrowing:
        adds = sorted(fired & NOT_NARROWING)
        if not adds:
            return [], bad
        probs.append(f"`{WITNESS_KEY}: {narrowing[0]}`: a narrowing adds no trust, but the change adds "
                     f"{', '.join('`' + a + '`' for a in adds)}")
    else:
        probs.append(f"no valid `{WITNESS_KEY}:` trailer")
    return probs + bad, []

def witness_gate(argv, paths_only=False):
    """`--witness-gate A..B`: check the gate on a range (land.sh passes origin/lean..HEAD);
    exit 1 if it refuses. `--witness-paths A..B`: print the range's witness paths that land.sh
    must exercise, one per line, with their location kind."""
    if not argv or ".." not in argv[0]:
        sys.exit("trusted-delta: --witness-gate/--witness-paths take a range A..B")
    rng = argv[0]
    head = rng.split("..", 1)[1].lstrip(".") or "HEAD"
    witnesses = commit_trailers(rng, WITNESS_KEY)
    def exists(p):
        return subprocess.run(["git", "cat-file", "-e", f"{head}:{p}"], cwd=ROOT,
                              capture_output=True).returncode == 0
    if paths_only:
        for w in witnesses:
            if exists(w) and witness_location(w):
                print(f"{witness_location(w)} {w}")
        return 0
    real_uses = commit_trailers(rng, REAL_USE_KEY)
    _, diff_args, rev_new, rev_old = resolve_target([rng])
    triggers = gate_triggers(parse_diff(diff_args), rev_old, rev_new)
    if not triggers:
        print("witness gate: no semantics addition (no gated signal on an added tier-0 line): pass")
        return 0
    print(f"witness gate: {len(triggers)} gated line(s) (criterion 1, "
          f".agents/skills/review-trusted/CRITERIA.md):")
    for p, ln, name, text in triggers[:40]:
        print(f"  `{name}` {p}:{ln}: {text[:140]}")
    if len(triggers) > 40:
        print(f"  ... and {len(triggers) - 40} more")
    for w in witnesses:
        print(f"  {WITNESS_KEY}: {w}")
    for r in real_uses:
        print(f"  {REAL_USE_KEY}: {r}")
    probs, warns = check_witness(triggers, witnesses, real_uses, exists)
    for w in warns:
        print(f"witness gate: warning (another trailer satisfies the gate): {w}")
    for pr in probs:
        print(f"witness gate: REFUSED: {pr}")
    if probs:
        print(f"Add to a commit message of the branch (its last paragraph):\n"
              f"  {WITNESS_KEY}: <goose/testdata/examples/...go | Perennial/ProgramLogic/...Test.lean"
              f" | Perennial/Proof/...lean>\n"
              f"  {REAL_USE_KEY}: <repo>:<package>.<function>\n"
              f"or, for a change that only removes trust or makes the model stuck in more places,\n"
              f"  {WITNESS_KEY}: none (narrowing: <reason>)")
        return 1
    print("witness gate: pass (the review checks that the witness needs the addition: CRITERIA.md, 1)")
    return 0

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
        "model-table": ["[model]", "  [model]  # the overlay"],
        "model-replaces": ['replaces = ["Mutex.Lock", "init.0"]', "replaces = []", 'replaces = ["*"]',
                           'added_methods = ["*.PbModel*"]', "  replaces = ["],
        "gomodel-replace": ['//gomodel:replace init.0 "x := 1"', '  //gomodel:replace init.12 "f()"'],
        "gomodel-choice": ["\tif gomodel.Choose() {", "\tn := gomodel.ChooseUint64()",
                           "\t\tgomodel.Stuck()", "return gomodel.Choose ()"],
    }
    must_not = {
        "step-rule": ["  intro _ _ _ h; exact h.isGoStep_det_internal",
                      "  float64Encodes (float64Add v1 v2) f"],
        "axiom": ["  -- the axiom of choice", "#print axioms foo"],
        "semantics-class": ["noncomputable instance runeStruct.zero_val [GooseExts] : ZeroVal runeStruct :=",
                            "instance [GoSemanticsFunctions] (T : go.GoType) : Foo T := ⟨⟩"],
        "model-table": ["[[model]]", "[models]", 'dir = "[model]"'],
        "model-replaces": ["\treplaces := m.Replaces", "\treplaces = m.Replaces", "# replaces = [\"x\"]",
                           "my_replaces = []"],
        "gomodel-replace": ["// gomodel replaces init.0", "//gomodel:replacement"],
        "gomodel-choice": ['import "internal/gomodel"', "gomodel.ChooseN()", "x.Choose()",
                           "notgomodel.Stuck()"],
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
    # skipped' entries: Lean string literals, a `⟩` or `]` inside one, the decl field
    gen = "\n".join([
        "noncomputable def skipped' : List go.SkippedVar := [",
        '  ⟨"p.X", "a \\"reason\\" with ⟩ and ]", "var X = f()"⟩,',
        '  ⟨"p._@a.go:3", "an interface check\\nover two lines", "var _ I = (*T)(nil)"⟩]',
        "",
        "noncomputable instance info' : PkgInfo pkg_id.p where",
    ])
    want = {"p.X": ('a "reason" with ⟩ and ]', "var X = f()"),
            "p._@a.go:3": ("an interface check\nover two lines", "var _ I = (*T)(nil)")}
    if skipped_entries(gen) != want:
        bad.append(f"skipped_entries: {skipped_entries(gen)!r}")
    # a Go model directive is code, not prose; the rest of is_prose is unchanged
    if is_prose("m.go", '//gomodel:replace init.0 "x := 1"') or not is_prose("a.lean", "-- c") \
            or not is_prose("c.toml", "# [model]") or is_prose("m.go", "\tgomodel.Stuck()"):
        bad.append("is_prose: a `//gomodel:` directive, or another line, misclassified")
    # the Go declaration extractor
    gosrc = "\n".join([
        "package p",                                              # 1
        "",
        'import "internal/gomodel"',
        "",
        "// MODEL: Lock may block forever; Go's",                 # 5
        "// mutex too. A brace in a comment: {",
        "func (m *Mutex) Lock() {",
        '\ts := "}{" + `raw }',
        "still raw {`",
        "\tif gomodel.Choose() { /* } */",                        # 10
        "\t}",
        "}",
        "",
        "func (s *Set[K, V]) Len() int { return 0 }",
        "",                                                        # 15
        "func helper(",
        "\ta int,",
        ") int {",
        "\treturn a",
        "}",                                                       # 20
        "",
        "var (",
        "\t// x and y",
        "\tx, y = f(), '}'",
        "\tz = map[int]int{",                                     # 25
        "\t\t1: 2,",
        "\t}",
        ")",
        "",
        "type T struct {",                                         # 30
        "\tf int",
        "}",
        "",
        '//gomodel:replace init.0 "registry = map[string]int{}"',
        "// MODEL: the same table.",                               # 35
        "func init() {",
        "}",
        "",
        "func init() {}",
        "",                                                        # 40
        "type (",
        "\tA int",
        "\tB = A",
        ")",
        "",
        "const C = 1",
        "",
        "func stub() bool { return false }",
    ])
    got = {n: (d["kind"], d["line"], d["text"].count("\n") + 1) for d in go_decls(gosrc) for n in d["names"]}
    want = {"Mutex.Lock": ("method", 5, 8), "Set.Len": ("method", 14, 1), "helper": ("func", 16, 5),
            "x": ("var", 23, 2), "y": ("var", 23, 2), "z": ("var", 25, 3), "T": ("type", 30, 3),
            "init.0": ("func", 34, 4), "init#1": ("func", 39, 1), "A": ("type", 42, 1),
            "B": ("type", 43, 1), "C": ("const", 46, 1), "stub": ("func", 48, 1)}
    if got != want:
        bad.append(f"go_decls: {got!r}")
    init0 = [d for d in go_decls(gosrc) if d["names"] == ["init.0"]]
    if not init0 or init0[0]["marker"] != '"registry = map[string]int{}"' \
            or not doc_starts_with_model(init0[0]["text"]):
        bad.append("go_decls: the `//gomodel:replace` marker or the `MODEL:` doc of init.0")
    if doc_starts_with_model("// Lock locks m.\nfunc (m *Mutex) Lock() {}"):
        bad.append("doc_starts_with_model: a plain doc comment accepted")
    # the [model] table and goose's pattern sets
    cfg_txt = "\n".join([
        'translate = ["*"]',
        'trusted = ["stub"]',
        "",
        "[model]",
        'dir = "goose/model/overlay/internal/sync/"',
        'replaces = ["Mutex.Lock", "init.0"]',
        'added_methods = ["*.PbModel*"]',
    ])
    if model_table(cfg_txt) != {"dir": "goose/model/overlay/internal/sync",
                                "replaces": ["Mutex.Lock", "init.0"], "added_methods": ["*.PbModel*"]}:
        bad.append(f"model_table: {model_table(cfg_txt)!r}")
    if model_table('translate = ["*"]') is not None or \
            model_table('[model]\ndir = "d"')["replaces"] is not None or \
            model_table('[model]\ndir = "d"\nreplaces = []')["replaces"] != []:
        bad.append("model_table: no table, a missing replaces, or an empty one")
    if not (pattern_contains(["*.PbModel*"], "T.PbModelMarshal") and not pattern_contains(["*.PbModel*"], "T.Marshal")
            and not pattern_contains(["*", "!x"], "x") and pattern_contains(["*", "!x"], "y")
            and pattern_contains(["stub"], "stub") and not pattern_contains(["stub"], "stubs")):
        bad.append("pattern_contains: goose's pattern-set semantics")
    # the witness gate (criterion 1): new GoInstruction constructors and the trailer check
    instr = "\n".join([
        "inductive GoUnaryOperator where",
        "  | GoPos | GoNeg",
        "inductive GoInstruction where",
        "  | AngelicExit",
        "  /-- doc -/",
        "  | AsAssign",
        "  | GoLoad (t : go.GoType)",
        "def f := 1",
    ])
    if new_instruction_hits(instr, [2, 4, 5, 6, 7, 8]) != [(4, "| AngelicExit"), (6, "| AsAssign"),
                                                          (7, "| GoLoad (t : go.GoType)")]:
        bad.append(f"new_instruction_hits: {new_instruction_hits(instr, [2, 4, 5, 6, 7, 8])!r}")
    rule = [("Perennial/Golang/Defn/X.lean", 3, "step-rule", "⟦GoUnOp GoPos t, #v⟧ ⤳ #v")]
    assume = rule + [("Perennial/GooseLang/Lang.lean", 9, "assume", "assume (n < 2^63)")]
    ex = {"goose/testdata/examples/semantics/plus.go", "Perennial/ProgramLogic/FooTest.lean",
          "Perennial/Proof/a/b.lean", "README.md", "goose/testdata/examples/semantics/x_test.go"}
    real = ["perennial:strconv.Itoa"]
    gate_cases = [  # (triggers, witnesses, real uses, passes)
        ([], [], [], True),
        (rule, [], [], False),
        (rule, ["goose/testdata/examples/semantics/plus.go"], real, True),
        (rule, ["Perennial/ProgramLogic/FooTest.lean"], real, True),
        (rule, ["Perennial/Proof/a/b.lean"], ["etcd-grove:go.etcd.io/raft/v3.(*raft).Step"], True),
        (rule, ["goose/testdata/examples/semantics/plus.go"], [], False),
        (rule, ["goose/testdata/examples/semantics/plus.go"], ["strconv.Itoa"], False),
        (rule, ["goose/testdata/examples/semantics/missing.go"], real, False),
        (rule, ["README.md"], real, False),
        (rule, ["goose/testdata/examples/semantics/x_test.go"], real, False),
        (rule, ["none (narrowing: the rule is now stuck on nil)"], [], True),
        (rule, ["none"], [], False),
        (rule, ["none (narrowing: )"], [], False),
        (assume, ["none (narrowing: tighter)"], [], False),
        (assume, ["goose/testdata/examples/semantics/plus.go"], real, True),
        # one valid witness suffices; an invalid or narrowing trailer of another commit only warns
        (assume, ["none (narrowing: x)", "goose/testdata/examples/semantics/missing.go",
                  "goose/testdata/examples/semantics/plus.go"], ["bad", "perennial:strings.Count"], True),
        (rule, ["goose/testdata/examples/semantics/missing.go", "none (narrowing: x)"], [], True),
        (rule, ["goose/testdata/examples/semantics/missing.go"], [], False),
    ]
    for trig, ws, rs, ok in gate_cases:
        probs, _ = check_witness(trig, ws, rs, lambda p: p in ex)
        if (not probs) != ok:
            bad.append(f"check_witness({[t[2] for t in trig]}, {ws}, {rs}): {probs!r}")
    for p, want in [("goose/testdata/examples/unittest/generics/g.go", "go-example"),
                    ("Perennial/ProgramLogic/ThreadTokensTest.lean", "lean"),
                    ("Perennial/ProgramLogic/Bounds.lean", None), ("goose/glang/x.go", None)]:
        if witness_location(p) != want:
            bad.append(f"witness_location({p}): {witness_location(p)!r}")
    for b in bad:
        print("FAIL " + b)
    print(f"trusted-delta self-test: {'FAILED' if bad else 'ok'}")
    return 1 if bad else 0

# --------------------------------------------------------------- main
def main(argv):
    if "--self-test" in argv:
        return self_test()
    if "--witness-gate" in argv or "--witness-paths" in argv:
        return witness_gate([a for a in argv if not a.startswith("--")], "--witness-paths" in argv)
    full = "--full" in argv
    nodiff = "--no-diff" in argv
    check = "--check" in argv
    argv = [a for a in argv if not a.startswith("--")]
    desc, diff_args, rev_new, rev_old = resolve_target(argv)
    files = parse_diff(diff_args)
    if not files:
        print(f"trusted-delta: {desc}: no changes")
        return 0

    tiered, model_owner_of = tier_files(files, rev_old, rev_new)

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
    cfg = [(p, kind) for p, kind in tiered[0] if kind in ("goose-config", "test-config")]
    if cfg:
        print("## goose configuration (trusted / translated / axiomatized / skipped)\n")
        for p, kind in cfg:
            lists, reasons, old_reasons = toml_lists(p, rev_old, rev_new)
            for key, added, removed in lists:
                print(f"- {p} `{key}`: added {added or '[]'}, removed {removed or '[]'}")
                if key == "skip":
                    pkg = config_pkg(p, rev_new)
                    for name in added:
                        print(f"  - skipped `{pkg}.{name}`: reason: \"{reasons.get(name, '')}\"")
                        print("    The reason must show that Go's initializer terminates, cannot panic "
                              "and has no effect beyond the variable; read its callees (an effect "
                              "on another variable or package, a registration, is not skippable).")
                        if name.startswith("_@"):
                            print("    (a blank `var _`, named by its position: its declaration is "
                                  "in the translation's `skipped'`, below)")
                            continue
                        src = go_source(f"{pkg}.{name}", unexported=True, cwd=config_go_dir(p))
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
                if key == "trusted" and kind == "goose-config":
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

    # skipped' entries of generated files
    nskipped = 0
    gen = [p for p, kind in tiered[1] if kind == "generated-code" and p.endswith(".lean")]
    deltas = [(p, d) for p in gen for d in [skipped_delta(p, rev_old, rev_new)] if d]
    if deltas:
        print("## Skipped package variables in generated code (TRUSTED)\n")
        print("Each entry of a `skipped'` list is a trusted claim (not running the variable's Go "
              "initializer is unobservable; rule R11): check every added or changed one against "
              "its Go declaration and its reason.\n")
        for p, d in deltas:
            print(f"### {p}\n")
            for sign, name, old, new in d:
                nskipped += 1
                word = {"+": "added", "-": "removed", "~": "changed"}[sign]
                print(f"- {word} `{name}`")
                fields = ("reason", "decl")
                for k, f in enumerate(fields):
                    o = old[k] if old and k < len(old) else None
                    n = new[k] if new and k < len(new) else None
                    if sign == "+" and n is not None:
                        print(f"  - {f}: {n!r}")
                    elif sign == "-" and o is not None:
                        print(f"  - {f} was: {o!r}")
                    elif sign == "~" and o != n:
                        print(f"  - {f}: {o!r} -> {n!r}")
            print()

    # Go model overlays: changed configs with a `[model]` table, and owners of changed model files
    mcfg = {p for p, kind in cfg if model_table(file_at(rev_new, p)) or model_table(file_at(rev_old, p))}
    for p in files:
        mcfg |= model_owner_of(p)
    if mcfg:
        print("## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)\n")
        print("For each replaced declaration: every behaviour of the real one (gc, linux/amd64, "
              "the pinned Go), under every use by the program and the real package, must be a "
              "behaviour of the model's translation. Compare the two sources line by line; every "
              "`gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.\n")
        for c in sorted(mcfg):
            report_model(c, rev_old, rev_new, files)

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

    if check and (tiered[0] or nskipped):
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
