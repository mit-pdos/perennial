#!/usr/bin/env python3

# coqc wrapper

from datetime import datetime
from os import path
import re
import sqlite3
import subprocess
import sys


class StdoutDb:
    def add_qed(self, fname, ident, time):
        base = path.basename(fname)
        if time > 0.1:
            print("{:15s} {:20s} {:0.2f}".format(base, ident, time))

    def add_file(self, fname, time):
        if time > 0.1:
            print("{} {:0.2f}".format(fname, time))

    def close(self):
        pass


class TimingDb:
    def __init__(self, conn):
        self.conn = conn

    @classmethod
    def from_file(cls, fname):
        conn = sqlite3.connect(fname, isolation_level=None)
        conn.execute(
            """CREATE TABLE IF NOT EXISTS qed_timings """
            + """(fname text NOT NULL, ident text NOT NULL, time real NOT NULL, """
            + """PRIMARY KEY (fname, ident) )"""
        )
        conn.execute(
            """CREATE TABLE IF NOT EXISTS file_timings """
            + """(fname text NOT NULL PRIMARY KEY, time real)"""
        )
        return cls(conn)

    def add_qed(self, fname, ident, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO qed_timings VALUES (?,?,?)""",
            (fname, ident, time),
        )

    def add_file(self, fname, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO file_timings VALUES (?,?)""", (fname, time)
        )

    def close(self):
        self.conn.close()


class CoqcFilter:
    DEF_RE = re.compile(
        r"""(Theorem|Lemma|Instance|Definition|Corollary|Remark|Fact)\s+"""
        + r"""(?P<ident>[a-zA-Z0-9'_]*)"""
    )
    TIME_RE = re.compile(
        r"""Chars (?P<start>[0-9]*) - (?P<end>[0-9]*) \[.*\] """
        + r"""(?P<time>[0-9.]*) secs .*"""
    )
    QED_RE = re.compile(r"""(Time)?\s*Qed\.""")

    def __init__(self, vfile, db):
        self.vfile = vfile
        self.db = db
        self.start = datetime.now()
        self.contents = None
        self.curr_def = None

    @classmethod
    def from_coqargs(cls, args, db):
        for arg in args:
            if arg.endswith(".v"):
                return cls(arg, db)
        return cls(None, db)

    def _read_vfile(self):
        with open(self.vfile) as f:
            self.contents = f.read()

    def chars(self, start, end):
        if not self.contents:
            self._read_vfile()
        return self.contents[start:end]

    def update_def(self, m):
        """Update current definition based on DEF_RE match."""
        self.curr_def = m.group("ident")

    def update_timing(self, m):
        """Add new timing info based on TIME_RE match."""
        start = int(m.group("start"))
        end = int(m.group("end"))
        time = float(m.group("time"))
        code = self.chars(start, end)
        m = self.DEF_RE.search(code)
        if m:
            return self.update_def(m)
        code = self.chars(start, end)
        if self.QED_RE.match(code):
            if self.curr_def is None:
                print(
                    self.vfile,
                    "no proof ident {} - {}".format(start, end),
                    file=sys.stderr,
                )
                return
            self.db.add_qed(self.vfile, self.curr_def, time)
            return

    def line(self, l):
        """Process a line of output from coqc."""
        line = l.decode("utf-8")
        m = self.TIME_RE.match(line)
        if m:
            return self.update_timing(m)

        print(line, end="")

    def done(self):
        delta = (datetime.now() - self.start).total_seconds()
        self.db.add_file(self.vfile, delta)
        self.db.close()


def read_coqproject(fname):
    args = []
    with open(fname) as f:
        for line in f:
            args.extend(line.rstrip().split(" "))
    return args


import argparse

parser = argparse.ArgumentParser()

parser.add_argument(
    "--proj", default=None, help="path to _CoqProject to use for options"
)

parser.add_argument("--timing-db", default=None, help="database to store timing info")

args, coq_args = parser.parse_known_args()

coqproject_file = args.proj
if coqproject_file is None and path.exists("_CoqProject"):
    coqproject_file = "_CoqProject"
if path.exists(coqproject_file):
    proj_args = read_coqproject(coqproject_file)
else:
    proj_args = []

if args.timing_db:
    db = TimingDb.from_file(args.timing_db)
else:
    db = StdoutDb()

args = ["coqc"]
args.extend(proj_args)
args.append("-time")
args.extend(coq_args)

filter = CoqcFilter.from_coqargs(coq_args, db)

p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=sys.stderr)
try:
    for line in iter(p.stdout.readline, b""):
        filter.line(line)
except KeyboardInterrupt:
    p.kill()
    p.wait()
    db.close()
    sys.exit(p.returncode)
filter.done()
sys.exit(p.returncode)
