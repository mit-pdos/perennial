#!/usr/bin/env python3

# coqc wrapper

from __future__ import print_function

from datetime import datetime
from os import path
import re
import sqlite3
import subprocess
import sys


class NullDb:
    def add_qed(self, fname, ident, time):
        pass

    def add_file(self, fname, is_vos, time):
        pass

    def close(self):
        pass


class StdoutDb:
    def add_qed(self, fname, ident, time):
        base = path.basename(fname)
        if time > 0.1:
            print("{:15s} {:20s} {:0.2f}".format(base, ident, time))

    def add_file(self, fname, _is_vos, time):
        if time > 0.1:
            print("{} {:0.2f}".format(fname, time))

    def close(self):
        pass


class TimingDb:
    def __init__(self, conn):
        self.conn = conn

    @classmethod
    def from_file(cls, fname):
        conn = sqlite3.connect(fname, isolation_level=None, timeout=20)
        conn.execute("""PRAGMA synchronous=off""")
        conn.execute(
            """CREATE TABLE IF NOT EXISTS qed_timings """
            + """(fname text NOT NULL, ident text NOT NULL, time real NOT NULL, """
            + """PRIMARY KEY (fname, ident) )"""
        )
        conn.execute(
            """CREATE TABLE IF NOT EXISTS file_timings """
            + """(fname text NOT NULL PRIMARY KEY, """
            + """is_vos integer NOT NULL, time real)"""
        )
        return cls(conn)

    def add_qed(self, fname, ident, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO qed_timings VALUES (?,?,?)""",
            (fname, ident, time),
        )

    def add_file(self, fname, is_vos, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO file_timings VALUES (?,?,?)""",
            (fname, is_vos, time),
        )

    def close(self):
        self.conn.close()


class Classify:
    DEF_RE = re.compile(
        r"""(?:#\[(local|global|export)\]\s+)?(?:(Local|Global)\s+)?(?:Theorem|Lemma|Instance|Definition|Corollary|Remark|Fact|Program Lemma|Proposition)\s+"""
        + r"""(?P<ident>\w(\w|')*)"""
    )
    OBLIGATION_RE = re.compile(r"""Next Obligation\.""")
    GOAL_RE = re.compile(r"""\s*Goal\s+""")
    TIME_RE = re.compile(
        r"""Chars (?P<start>\d*) - (?P<end>\d*) \[.*\] """
        + r"""(?P<time>[0-9.]*) secs .*"""
    )
    QED_RE = re.compile(r"""(?:Time\s*)?Qed\.""")
    obligation_count = 0
    goal_count = 0

    @classmethod
    def is_qed(cls, s):
        return cls.QED_RE.match(s) is not None

    @classmethod
    def get_def(cls, s):
        m = cls.DEF_RE.match(s)
        if m is not None:
            return m.group("ident")
        m = cls.OBLIGATION_RE.match(s)
        if m is not None:
            cls.obligation_count += 1
            return "<obligation {}>".format(cls.obligation_count)
        m = cls.GOAL_RE.match(s)
        if m is not None:
            cls.goal_count += 1
            return "<goal {}>".format(cls.goal_count)
        return None

    @classmethod
    def get_time(cls, s):
        m = cls.TIME_RE.match(s)
        if m is None:
            return None
        return (
            int(m.group("start")),
            int(m.group("end")),
            float(m.group("time")),
        )


class CoqcFilter:
    def __init__(self, vfile, is_vos, db, contents, start):
        self.vfile = vfile
        self.is_vos = is_vos
        self.contents = contents
        self.db = db
        self.start = start
        self.curr_def = None

    @classmethod
    def from_coqargs(cls, args, db, contents=None, start=None):
        is_vos = "-vos" in args
        vfile = None
        for arg in args:
            if arg.endswith(".v"):
                vfile = arg
                break
        if start is None:
            start = datetime.now()
        return cls(vfile, is_vos, db, contents, start)

    @classmethod
    def from_contents(cls, contents, db, start=None):
        return cls("<in-memory>.v", False, db, contents, start)

    def _read_vfile(self):
        with open(self.vfile, "rb") as f:
            self.contents = f.read()

    def chars(self, start, end):
        if not self.contents:
            self._read_vfile()
        return self.contents[start:end].decode("utf-8")

    def update_def(self, ident):
        """Update current definition to ident."""
        self.curr_def = ident

    def update_timing(self, timing_info):
        """Add new timing info based on Classify.get_time."""
        start, end, time = timing_info
        code = self.chars(start, end)
        ident = Classify.get_def(code)
        if ident:
            return self.update_def(ident)
        if Classify.is_qed(code):
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
        timing_info = Classify.get_time(line)
        if timing_info:
            return self.update_timing(timing_info)

        sys.stdout.write(line)

    def done(self, end_t=None):
        if end_t is None:
            end_t = datetime.now()
        delta = (end_t - self.start).total_seconds()
        self.db.add_file(self.vfile, self.is_vos, delta)
        self.db.close()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--no-timing", action="store_true", help="disable all timing tracking"
    )

    parser.add_argument(
        "--timing-db", default=None, help="database to store timing info"
    )

    args, coq_args = parser.parse_known_args()

    if args.no_timing:
        db = NullDb()
    elif args.timing_db:
        db = TimingDb.from_file(args.timing_db)
    else:
        db = StdoutDb()

    args = ["coqc"]
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
    p.wait()
    sys.exit(p.returncode)
