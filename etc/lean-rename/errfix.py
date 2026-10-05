"""Build-error-driven fixer: `Unknown identifier `old`` at file:line:col -> new name."""
import re, sys, collections

ren = [l.rstrip("\n").split("\t") for l in open(sys.argv[1], encoding="utf-8") if "\t" in l]
log = open(sys.argv[2], encoding="utf-8").read()


def split_name(n):
    return re.split(r"\.(?![^«]*»)", n)


rep = {}
for o, n in ren:
    oc, nc = split_name(o), split_name(n)
    if oc[0] == "Perennial":
        oc, nc = oc[1:], nc[1:]
    extra = len(nc) - len(oc)
    for k in range(1, len(oc) + 1):
        os_ = ".".join(oc[-k:])
        ns_ = ".".join(nc[-(k + extra):])
        if os_ != ns_:
            rep.setdefault(os_, set()).add(ns_)
amb = {k for k, v in rep.items() if len(v) > 1}
rep = {k: next(iter(v)) for k, v in rep.items() if len(v) == 1}

ERR = re.compile(r"^error: (Perennial/[^:]+\.lean):(\d+):(\d+): (?:Unknown identifier|unknown identifier|Unknown constant|unknown constant|Unknown namespace|unknown namespace) [`']([^`']+)[`']", re.M)
fixes = collections.defaultdict(list)
unresolved = []
for f, l, c, name in ERR.findall(log):
    name = name.replace("✝", "")
    nm = name[len("Perennial."):] if name.startswith("Perennial.") else name
    if nm in rep:
        fixes[f].append((int(l) - 1, int(c), nm, rep[nm]))
    else:
        # dotted access `x.old`: try the last component
        last = split_name(nm)[-1]
        if last in rep and "." not in rep[last]:
            fixes[f].append((int(l) - 1, int(c), last, rep[last]))
        else:
            unresolved.append((f, l, c, name, "ambiguous" if nm in amb or last in amb else ""))
n = 0
for f, lst in fixes.items():
    lines = open(f, encoding="utf-8").read().split("\n")
    for (l, c, old, new) in sorted(set(lst), reverse=True):
        line = lines[l]
        # find the token at/after column c (columns are codepoints in Lean messages)
        m = re.compile(r"(?<![\w'])" + re.escape(old) + r"(?![\w'])").search(line, max(0, c - len(old)))
        if m:
            lines[l] = line[:m.start()] + new + line[m.end():]
            n += 1
        else:
            unresolved.append((f, l + 1, c, old, "token not found"))
    open(f, "w", encoding="utf-8").write("\n".join(lines))
print("fixed", n)
for u in unresolved[:60]:
    print("UNRESOLVED", u)

# hygienic names (`foo✝`) and other leftovers: the identifier is in a quotation,
# possibly in another file; replace the multi-word old name everywhere in
# hand-written files
import subprocess
left = sorted({u[3].replace("✝", "") for u in unresolved})
left = [x[len("Perennial."):] if x.startswith("Perennial.") else x for x in left]
left = [x for x in left if x in rep and "_" in x.split(".")[-1]]
if left:
    files = subprocess.run(["git", "ls-files", "Perennial/*.lean"], capture_output=True, text=True).stdout.split()
    pat = re.compile(r"(?<![\w'.])(" + "|".join(map(re.escape, sorted(left, key=len, reverse=True))) + r")(?![\w'])")
    for f in files:
        if f.startswith(("Perennial/Code/", "Perennial/GeneratedProof/", "Perennial/TrustedCode/", "Perennial/ManualProof/")):
            continue
        s = open(f, encoding="utf-8").read()
        ns, c = pat.subn(lambda m: rep[m.group(1)], s)
        if c:
            print("GLOBAL", f, c, sorted(set(pat.findall(s))))
            open(f, "w", encoding="utf-8").write(ns)
