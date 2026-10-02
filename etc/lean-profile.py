#!/usr/bin/env python3
"""Profile Lean elaboration of Perennial files.

For each given module (``Perennial.Golang.Theory.Slice``) or file
(``Perennial/Golang/Theory/Slice.lean``), runs

    lake env lean --json -Dprofiler=true -Dprofiler.threshold=T FILE

(which re-elaborates the file against the existing .olean files of its imports,
without writing anything) and reports

* wall time, peak RSS (flagged when above 4GB) and errors per file;
* the top-N declarations by profiled time, split by category (tactic
  execution, type checking = kernel, simp, typeclass inference, ...).

A watchdog kills a run whose resident memory exceeds ``--mem-cap`` (default
12GB).  (``ulimit -v`` cannot be used: Lean reserves address space for its
thread stacks and fails to start threads.)

Usage:
    etc/lean-profile.py [options] MODULE_OR_FILE...
      -t/--threshold MS   per-item profiler threshold (default 200)
      -n/--top N          declarations to show per file (default 15)
      -j/--jobs J         files to run in parallel (default 1)
      --mem-cap GB        kill a run above this RSS (default 12)
      --build-deps        `lake build` the imports of each file first
      --save F.json       save results (for --compare)
      --compare F.json    print a before/after table against saved results
      --md                print the summary as a markdown table
      --root DIR          the Lake project to run in (default: this checkout)

Example:
    etc/lean-profile.py --save /tmp/base.json Perennial.Proof.math.bits
    ... edit ...
    etc/lean-profile.py --compare /tmp/base.json Perennial.Proof.math.bits
"""
import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque)\b\s*([^\s:({\[]*)")
MSG_RE = re.compile(r"^(.*?) took ([\d.]+)(ms|s)\s*$")


def to_file(m):
    if m.endswith(".lean"):
        return m
    return m.replace(".", "/") + ".lean"


def to_module(f):
    return f[:-5].replace("/", ".") if f.endswith(".lean") else f


def rss_tree_kb(pid):
    """Total RSS (kB) of pid and its descendants."""
    total = 0
    try:
        children = {}
        for p in os.listdir("/proc"):
            if not p.isdigit():
                continue
            try:
                with open(f"/proc/{p}/stat") as fh:
                    st = fh.read()
                ppid = int(st[st.rfind(")") + 2:].split()[1])
                children.setdefault(ppid, []).append(int(p))
            except OSError:
                pass
        stack = [pid]
        while stack:
            q = stack.pop()
            try:
                with open(f"/proc/{q}/statm") as fh:
                    total += int(fh.read().split()[1]) * os.sysconf("SC_PAGE_SIZE") // 1024
            except OSError:
                pass
            stack.extend(children.get(q, []))
    except OSError:
        pass
    return total


def decl_index(path):
    """line number (1-based) -> declaration name, for the enclosing declaration."""
    names = []
    try:
        with open(os.path.join(ROOT, path)) as fh:
            lines = fh.read().split("\n")
    except OSError:
        return lambda line: f"line {line}"
    cur = None
    for i, l in enumerate(lines, 1):
        m = DECL_RE.match(l)
        if m:
            cur = f"{m.group(1)} {m.group(2)}".strip() if m.group(2) else m.group(1)
            cur = f"{cur} (l.{i})"
        names.append(cur)

    def lookup(line):
        if 1 <= line <= len(names) and names[line - 1]:
            return names[line - 1]
        return f"line {line}"
    return lookup


def build_deps(path):
    mods = []
    with open(os.path.join(ROOT, path)) as fh:
        for l in fh:
            m = re.match(r"^import\s+(\S+)", l)
            if m:
                mods.append(m.group(1))
    mods = [m for m in mods if m.startswith("Perennial")]
    if mods:
        subprocess.run(["lake", "build", *mods], cwd=ROOT, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)


def run_one(path, args):
    if args.build_deps:
        build_deps(path)
    cmd = ["lake", "env", "lean", "--json", "-Dprofiler=true",
           f"-Dprofiler.threshold={args.threshold}", path]
    t0 = time.time()
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True)
    peak = [0]
    killed = [False]
    done = threading.Event()

    def watch():
        while not done.is_set():
            r = rss_tree_kb(proc.pid)
            peak[0] = max(peak[0], r)
            if r > args.mem_cap * 1024 * 1024:
                killed[0] = True
                subprocess.run(["pkill", "-9", "-P", str(proc.pid)])
                proc.kill()
                return
            done.wait(0.5)
    th = threading.Thread(target=watch, daemon=True)
    th.start()
    out, _ = proc.communicate(timeout=args.timeout)
    done.set()
    wall = time.time() - t0
    lookup = decl_index(path)
    decls = defaultdict(lambda: defaultdict(float))
    errors = []
    cumulative = {}
    in_cum = False
    for line in out.splitlines():
        if line.startswith("{"):
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                continue
            if msg.get("severity") == "error":
                errors.append(f"{msg['pos']['line']}: {msg['data'].strip()[:200]}")
                continue
            m = MSG_RE.match(msg.get("data", "").strip())
            if m and msg.get("severity") == "information":
                secs = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
                cat = m.group(1)
                cat = re.sub(r"^tactic execution of .*", "tactic", cat)
                decls[lookup(msg["pos"]["line"])][cat] += secs
            continue
        if line.startswith("cumulative profiling times"):
            in_cum = True
            continue
        if in_cum:
            m = re.match(r"^\s+(.*) ([\d.]+)(ms|s)$", line)
            if m:
                cumulative[m.group(1)] = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
        elif "error" in line.lower() and not line.startswith("{"):
            errors.append(line[:200])
    # tactic-execution messages are nested; report the max nesting level honestly by
    # keeping categories separate (a decl's "tactic" total may double count nested tactics)
    return {
        "file": path, "wall": wall, "peak_kb": peak[0], "killed": killed[0],
        "rc": proc.returncode, "errors": errors, "cumulative": cumulative,
        "decls": {d: dict(c) for d, c in decls.items()},
    }


def fmt_mem(kb):
    return f"{kb / 1024 / 1024:.1f}G"


def report(results, args):
    for r in results:
        flag = "  ** >4GB **" if r["peak_kb"] > 4 * 1024 * 1024 else ""
        status = "KILLED (mem cap)" if r["killed"] else (
            "ok" if r["rc"] == 0 and not r["errors"] else f"rc={r['rc']} errors={len(r['errors'])}")
        print(f"\n=== {r['file']}: {r['wall']:.1f}s wall, peak {fmt_mem(r['peak_kb'])}{flag}, {status}")
        for e in r["errors"][:5]:
            print(f"    error {e}")
        cum = r["cumulative"]
        top = sorted(((v, k) for k, v in cum.items() if k != "import"), reverse=True)[:6]
        print("    cumulative: " + ", ".join(f"{k} {v:.1f}s" for v, k in top))
        ds = sorted(r["decls"].items(), key=lambda kv: -max(kv[1].values()))[: args.top]
        for d, cats in ds:
            parts = ", ".join(f"{k} {v:.1f}s" for k, v in sorted(cats.items(), key=lambda kv: -kv[1]))
            print(f"    {max(cats.values()):7.1f}s  {d}: {parts}")
    print()
    if args.md:
        print("| file | wall (s) | peak RSS | kernel (s) | tactic (s) | simp (s) | TC (s) |")
        print("|---|---|---|---|---|---|---|")
        for r in results:
            c = r["cumulative"]
            print(f"| {to_module(r['file'])} | {r['wall']:.1f} | {fmt_mem(r['peak_kb'])} | "
                  f"{c.get('type checking', 0):.1f} | {c.get('tactic execution', 0):.1f} | "
                  f"{c.get('simp', 0):.1f} | {c.get('typeclass inference', 0):.1f} |")


def compare(results, base):
    bmap = {b["file"]: b for b in base}
    print("| file | before (s) | after (s) | speedup | RSS before | RSS after |")
    print("|---|---|---|---|---|---|")
    for r in results:
        b = bmap.get(r["file"])
        if not b:
            continue
        sp = b["wall"] / r["wall"] if r["wall"] else 0
        print(f"| {to_module(r['file'])} | {b['wall']:.1f} | {r['wall']:.1f} | {sp:.2f}x | "
              f"{fmt_mem(b['peak_kb'])} | {fmt_mem(r['peak_kb'])} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("targets", nargs="+")
    ap.add_argument("-t", "--threshold", type=int, default=200)
    ap.add_argument("-n", "--top", type=int, default=15)
    ap.add_argument("-j", "--jobs", type=int, default=1)
    ap.add_argument("--mem-cap", type=float, default=12)
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--build-deps", action="store_true")
    ap.add_argument("--save")
    ap.add_argument("--compare")
    ap.add_argument("--md", action="store_true")
    ap.add_argument("--root")
    args = ap.parse_args()
    if args.root:
        global ROOT
        ROOT = os.path.abspath(args.root)
    files = list(dict.fromkeys(to_file(t) for t in args.targets))  # dedupe: never run a file twice
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        results = list(ex.map(lambda f: run_one(f, args), files))
    report(results, args)
    if args.save:
        with open(args.save, "w") as fh:
            json.dump(results, fh, indent=1)
    if args.compare:
        with open(args.compare) as fh:
            compare(results, json.load(fh))


if __name__ == "__main__":
    main()
