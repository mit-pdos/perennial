#!/usr/bin/env python3
"""Trust delta of a change: which trusted files it touches and what it adds to
the trusted base. Input to the `review-trusted` skill
(.agents/skills/review-trusted/SKILL.md); it does not judge, it reports.

Usage: etc/trusted-delta.py [TARGET] [--full] [--no-diff] [--check]

  TARGET     a commit (reviews that commit: COMMIT^..COMMIT), a range A..B, or
             nothing: the working tree against the merge base with origin/lean
             (committed and uncommitted work of the current branch)
  --full     print the diff of every changed file, not only the trusted ones
  --no-diff  print only the summary and the signal lines
  --check    exit 1 if the change touches the trusted base (tier 0) at all,
             for use in hooks

Tiers (see the skill): 0 = trusted (semantics, translator, trusted models,
goose configuration); 1 = generated (trusted through goose; hand edits are
suspect); 2 = program logic and libraries (proved, but can hide trust in an
axiom/sorry/opaque); 3 = proofs, docs, tooling.

For every added line the report flags *signals*: constructs that add to or
move the trusted base (assume, axiom, sorry, opaque, native_decide, ...) and
constructs that change what the model does (Panic, AngelicExit, a new step
rule, a new trusted `.impl`, a `trusted =` list, ...). For a new or changed
trusted model whose docstring quotes Go code, it prints the real Go source of
the function (`go doc -src`) next to it, when the Go toolchain can find it.
"""
import os, re, subprocess, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

# --------------------------------------------------------------- tiers
TIER0 = [
    ("semantics", r"^Perennial/GooseLang/(Lang|BoundedLang|Adequacy|Threads|Receipts|Locations|Ext|CrashLang|CrashAdequacy|DistLang|DistAdequacy)\.lean$"),
    ("semantics", r"^Perennial/GooseLang/Ext/"),
    ("semantics", r"^Perennial/Golang/Defn/"),
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
# (name, regex on an added/removed line, why it matters)
SIGNALS = [
    ("axiom", r"^\s*(noncomputable\s+)?axiom\b", "a new axiom: trusted outright"),
    ("sorry", r"\bsorry\b|\bsorryAx\b", "an unproved obligation; in tiers 0-2 it is an axiom"),
    ("opaque", r"^\s*(noncomputable\s+)?opaque\b", "an opaque constant: a value nobody can inspect"),
    ("native", r"native_decide|bv_decide|ofReduceBool|Lean\.ofReduceBool", "trusts native code (forbidden by README)"),
    ("implemented_by", r"implemented_by|@\[extern", "runtime behaviour differs from the definition"),
    ("unsafe", r"^\s*unsafe\s+(def|theorem)|\bunsafe\s+def\b", "Lean unsafe definition"),
    ("partial", r"^\s*partial\s+def\b", "partial def: an opaque constant in disguise"),
    ("assume", r"\bassume\b|\w*[aA]ssume(No|Mul|Sum)\w*", "a model assumption: must be unreachable in Go (README, Model assumptions)"),
    ("angelic", r"AngelicExit", "an angelic exit: the model refuses to continue (sound only if Go cannot reach it)"),
    ("panic", r"\bPanic\s+\"|Panic \(|\bgo\.panic\b|PanicV", "a (stuck) run-time panic in the model"),
    ("step-rule", r"⤳|⤳\[|HeadStep|base_step|BaseStep|\bFuncUnfold\b", "a semantics rule or unfolding"),
    ("semantics-class", r"^\s*class\s+\w*Semantics\b|^\s*instance\b.*Semantics", "a semantics class or its instance"),
    ("adequacy", r"\bgoose_(adequacy|invariance|init)\w*\b|GooseGpreS|receiptBound|threadBound", "an adequacy theorem or its parameters"),
    ("trusted-impl", r"\.impl\w*\s*(\[.*\])?\s*:\s*val\b|\.implWith\b", "a hand-written model of Go code"),
    ("trusted-list", r"^\s*trusted\s*=|^\s*\"!|^\s*translate\s*=|trust_proofgen|^\s*axiomatize\s*=", "goose configuration: what is trusted/translated/axiomatized"),
    ("extension", r"\bExtSemantics\b|\bGooseSemantics\b|\bextStep\w*|\bGooseExt\b", "an extension's semantics (new primitive operations)"),
    ("set_option", r"^\s*set_option\b", "an option change (linters off, max heartbeats, ...)"),
    ("verbatim", r"VerbatimExpr|Verbatim", "goose emits Lean text verbatim"),
]

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
    new_ln, in_comment = 0, False
    for line in raw.split("\n"):
        if line.startswith("diff --git"):
            m = re.match(r"diff --git a/(.*) b/(.*)$", line)
            path = m.group(2)
            cur = files[path] = {"status": "M", "lines": [], "raw": [line]}
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
            m = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)", line)
            new_ln = int(m.group(1))
        elif line.startswith("+") and not line.startswith("+++"):
            cur["lines"].append((new_ln, "+", line[1:], prose))
            new_ln += 1
        elif line.startswith("-") and not line.startswith("---"):
            cur["lines"].append((new_ln, "-", line[1:], prose))
        elif line.startswith(" "):
            new_ln += 1
    for f in files.values():
        f["raw"] = "\n".join(f["raw"])
    return files

# --------------------------------------------------------------- Go source lookup
def go_source(symbol):
    """`go doc -src strings.Split`; '' if the toolchain cannot find it."""
    # read-only: never let `go doc` rewrite go.sum / go.work.sum
    env = dict(os.environ, GOFLAGS="-mod=readonly", GOWORK="off")
    try:
        r = subprocess.run(["go", "doc", "-src", symbol], cwd=ROOT, capture_output=True,
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
    def lists(text):
        d = {}
        for key in ("translate", "trusted", "axiomatize"):
            m = re.search(r"^\s*" + key + r"\s*=\s*\[(.*?)\]", text, re.S | re.M)
            if m:
                items = re.findall(r'"([^"]*)"', m.group(1))
                d[key] = items
        m = re.search(r"^\s*trust_proofgen\s*=\s*(\w+)", text, re.M)
        if m:
            d["trust_proofgen"] = [m.group(1)]
        return d
    def show(rev):
        if rev is None:
            try:
                return open(os.path.join(ROOT, path)).read()
            except OSError:
                return ""
        r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else ""
    old, new = lists(show(rev_old)), lists(show(rev_new))
    out = []
    for key in sorted(set(old) | set(new)):
        o, n = old.get(key, []), new.get(key, [])
        if o != n:
            out.append((key, [x for x in n if x not in o], [x for x in o if x not in n]))
    return out

# --------------------------------------------------------------- main
def main(argv):
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
            for ln, s, text, prose in files[p]["lines"]:
                if prose:
                    continue
                for name, why in signals_in(text):
                    hits.append((ln, s, name, text.strip()))
            if not hits:
                continue
            nsig += len(hits)
            print(f"### {p}  (tier {t}, {kind})")
            seen = set()
            for ln, s, name, text in hits:
                key = (ln, s, name)
                if key in seen:
                    continue
                seen.add(key)
                loc = f"{p}:{ln}" if s == "+" else f"{p}:{ln} (removed)"
                print(f"- `{name}` {loc}: `{text[:160]}`")
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
        print("## goose configuration (trusted / translated / axiomatized)\n")
        for p, _ in cfg:
            for key, added, removed in toml_lists(p, rev_old, rev_new):
                print(f"- {p} `{key}`: added {added or '[]'}, removed {removed or '[]'}")
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
