"""After a --map rename: a declaration `structure _root_.Perennial.P.X` sitting alone in
`namespace X ... end X` (or `namespace x`, `namespace X_y` for `XY`; inside namespace P) is
unwrapped to `structure X`.

Usage: etc/lean-rename/unwrap.py FILE...
"""
import re, sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*"
                  r"(def|abbrev|theorem|lemma|instance|structure|inductive|class|axiom|opaque)\b")
for f in sys.argv[1:]:
    lines = open(f, encoding="utf-8").read().split("\n")
    changed = False
    i = 0
    while i < len(lines):
        m = re.match(r"^(?:(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*)"
                     r"(?:def|abbrev|structure|inductive|class|axiom|opaque) _root_\.Perennial\.([\w.'«»]+)", lines[i])
        if not m:
            i += 1
            continue
        full = m.group(1)
        short = full.rsplit(".", 1)[-1]
        # enclosing `namespace short` (closest preceding unmatched namespace line)
        j = i - 1
        while j >= 0 and not re.match(r"^namespace\s+(\S+)\s*$", lines[j]):
            j -= 1
        if j < 0:
            i += 1
            continue
        ns = lines[j].split()[1]
        parent = full.rsplit(".", 1)[0] if "." in full else ""
        # the namespace must be the old home of the type (`X` or the lowercase `x`)
        # and sit directly in the type's new parent
        if "." in ns or ns.lower() != short.lower().replace("_", "") and ns.replace("_", "").lower() != short.lower():
            i += 1
            continue
        k = i + 1
        while k < len(lines) and lines[k].strip() != f"end {ns}":
            k += 1
        block = lines[j + 1:k]
        decls = [l for l in block if DECL.match(l)]
        # doc comments directly above the namespace line stay attached to the declaration
        if k < len(lines) and len(decls) == 1:
            lines[i] = lines[i].replace("_root_.Perennial." + full, short, 1)
            del lines[k]
            del lines[j]
            changed = True
            i = j
        else:
            i += 1
    if changed:
        open(f, "w", encoding="utf-8").write("\n".join(lines))
        print("unwrapped in", f)
