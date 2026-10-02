#!/usr/bin/env python3
"""Summarize the Lean port: per-area file counts, sorry counts, and the Rocq
files (hand-written, under master's new/ and needed src/) without a Lean port.

Usage: etc/lean-port-status.py [--rocq PATH_TO_MASTER_CHECKOUT]
"""
import argparse, os, re, collections

ap = argparse.ArgumentParser()
ap.add_argument("--rocq", default=None, help="path to a checkout of master (for coverage)")
args = ap.parse_args()

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lean_root = os.path.join(root, "Perennial")
area = collections.defaultdict(lambda: [0, 0, 0])  # files, lines, sorries
sorry_re = re.compile(r"\bsorry\b")
for dp, _, fs in os.walk(lean_root):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, lean_root).split(os.sep)
        key = "/".join(rel[:2]) if len(rel) > 2 else rel[0]
        s = open(p, errors="ignore").read()
        s_nocomment = re.sub(r"/-.*?-/", "", s, flags=re.S)
        s_nocomment = re.sub(r"--.*", "", s_nocomment)
        a = area[key]
        a[0] += 1; a[1] += s.count("\n"); a[2] += len(sorry_re.findall(s_nocomment))
print(f"{'area':45} {'files':>6} {'lines':>8} {'sorry':>6}")
for k in sorted(area):
    f, l, so = area[k]
    print(f"{k:45} {f:6} {l:8} {so:6}")
tot = [sum(v[i] for v in area.values()) for i in range(3)]
print(f"{'TOTAL':45} {tot[0]:6} {tot[1]:8} {tot[2]:6}")

if args.rocq:
    def camel(seg):
        return "".join(w[:1].upper() + w[1:] for w in seg.split("_"))
    lean_files = set()
    for dp, _, fs in os.walk(lean_root):
        for f in fs:
            if f.endswith(".lean"):
                lean_files.add(os.path.relpath(os.path.join(dp, f), lean_root)[:-5].lower().replace("_", ""))
    missing = []
    for sub in ["golang", "ghost", "proof", "trusted_code", "manualproof"]:
        for dp, _, fs in os.walk(os.path.join(args.rocq, "new", sub)):
            for f in fs:
                if not f.endswith(".v") or "__nobuild" in f:
                    continue
                rel = os.path.relpath(os.path.join(dp, f), os.path.join(args.rocq, "new"))[:-2]
                key = rel.lower().replace("_", "")
                key = key.replace("trustedcode", "trustedcode").replace("manualproof", "manualproof")
                if not any(lf.endswith(key.split("/", 1)[1]) for lf in lean_files):
                    missing.append(rel)
    print(f"\nRocq new/ files without an obvious Lean counterpart: {len(missing)}")
    for m in sorted(missing):
        print("  ", m)
