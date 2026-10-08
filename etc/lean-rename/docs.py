"""Update the prose and examples of docs/ and README.md to the renamed Lean names.

Usage: etc/lean-rename/docs.py FILE...
"""
import re, sys, os

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
ren = [l.rstrip("\n").split("\t") for l in open(os.path.join(ROOT, "etc/lean-rename/renames.tsv"), encoding="utf-8")
       if "\t" in l]


def sp(n):
    return re.split(r"\.(?![^«]*»)", n)


# multi-word / qualified names from the table (unique spellings only)
table = {}
for o, n in ren:
    oc, nc = sp(o)[1:], sp(n)[1:]
    if len(oc) == len(nc):
        for k in range(1, len(oc) + 1):
            a, b = ".".join(oc[-k:]), ".".join(nc[-k:])
            if a != b and ("_" in a.split(".")[-1] or k > 1):
                table.setdefault(a, set()).add(b)
table = {a: next(iter(b)) for a, b in table.items() if len(b) == 1}
single = {"go.type": "go.GoType", "loc": "Loc", "expr": "Expr", "heapGS": "HeapGS",
          "gooseGlobalGS": "GooseGlobalGS", "gooseLocalGS": "GooseLocalGS", "receiptGS": "ReceiptGS",
          "receiptGpreS": "ReceiptGpreS", "gooseGpreS": "GooseGpreS", "allG": "AllG",
          "ffi_syntax": "FfiSyntax", "go_string": "GoString"}
table.update(single)
tok = re.compile(r"(?<![\w'.])(" + "|".join(map(re.escape, sorted(table, key=len, reverse=True))) + r")(?![\w'])")

for f in sys.argv[1:]:
    s = open(f, encoding="utf-8").read()
    o = s
    # encodings
    s = re.sub(r"«([A-Za-z_][\w']*)__([A-Za-z_][\w']*)ⁱᵐᵖˡ»", r"\1.\2.impl", s)
    s = re.sub(r"«([A-Za-z_][\w']*)ⁱᵐᵖˡ»", r"\1.impl", s)
    s = re.sub(r"\b([A-Za-z_][\w']*)'fds_unsealed\b", r"\1.fieldsUnsealed", s)
    s = re.sub(r"\b([A-Za-z_][\w']*)'fds\b", r"\1.fields", s)
    s = re.sub(r"\bwp_([A-Z][A-Za-z0-9]*)__([A-Za-z_][\w']*)", r"\1.wp_\2", s)
    # descriptors in type positions, then value types X.t -> X
    s = re.sub(r"go\.type\.PointerType ([A-Z][A-Za-z0-9]*)\b(?!\.)", r"go.GoType.PointerType \1.ty", s)
    s = re.sub(r"def ([A-Z][A-Za-z0-9]*) : go\.type", r"def \1.ty : go.GoType", s)
    s = re.sub(r"\b((?:[a-z_][\w]*\.)*[A-Z][A-Za-z0-9]*)\.t\b(?!_)", r"\1", s)
    s = tok.sub(lambda m: table[m.group(1)], s)
    if s != o:
        open(f, "w", encoding="utf-8").write(s)
        print("updated", f)
