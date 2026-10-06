"""After renaming GooseLang's `expr` to `Expr`: meta code inside `namespace Perennial`
that said `Expr` (meaning `Lean.Expr`) now resolves to `Perennial.Expr`. Compare each
line with its version at REV token by token: a bare `Expr` that was already there at
REV is `Lean.Expr`.

Usage: etc/lean-rename/leanexpr.py REV
"""
import re, subprocess, sys

rev = sys.argv[1]
TOK = re.compile(r"(?<![\w'.])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)")
files = subprocess.run(["git", "grep", "-l", r"\bExpr\b", "--", "Perennial/*.lean"],
                       capture_output=True, text=True).stdout.split()
total = 0
for f in files:
    if f.startswith(("Perennial/Code/", "Perennial/GeneratedProof/")):
        continue
    old = subprocess.run(["git", "show", f"{rev}:{f}"], capture_output=True, text=True).stdout.split("\n")
    new = open(f, encoding="utf-8").read().split("\n")
    if len(old) != len(new):
        print("line count differs, skipped:", f)
        continue
    changed = False
    for i, (lo, ln) in enumerate(zip(old, new)):
        if "Expr" not in lo:
            continue
        to, tn = list(TOK.finditer(lo)), list(TOK.finditer(ln))
        if len(to) != len(tn):
            print(f"token count differs: {f}:{i + 1}")
            continue
        # replace from the right so positions stay valid
        for a, b in reversed(list(zip(to, tn))):
            if a.group(1) == "Expr" and b.group(1) == "Expr":
                ln = ln[:b.start()] + "Lean.Expr" + ln[b.end():]
                total += 1
                changed = True
        new[i] = ln
    if changed:
        open(f, "w", encoding="utf-8").write("\n".join(new))
print("Lean.Expr:", total)
