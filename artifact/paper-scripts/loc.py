#!/usr/bin/env python3

from __future__ import print_function

import sqlite3
import subprocess
import sys


class LineCountDb:
    def __init__(self, conn):
        self.conn = conn
        self.c = conn.cursor()

    def close(self):
        self.conn.close()

    @classmethod
    def count_lines(cls, src_dir):
        conn = sqlite3.connect(":memory:")
        done = subprocess.run(
            ["cloc", "--quiet", "--sql=-", "--include-lang=Coq,Go", "."],
            capture_output=True,
            # run in Armada source directory
            cwd=src_dir,
        )
        out = done.stdout.decode("utf-8")
        for c in out.split(";"):
            conn.execute(c)
        return cls(conn)

    def execute(self, *args):
        self.c.execute(*args)

    def loc(self, where):
        self.execute('select sum(nCode) as "LOC" from t where ({})'.format(where))
        return self.c.fetchone()[0]

    def files(self, where):
        files = []
        self.execute("select File, nCode from t where ({}) order by File".format(where))
        for row in self.c:
            filename = row[0]
            loc = row[1]
            files.append((filename, loc))
        return files


collections = {
    "Transition system DSL": r"""(File_dirname = "./vendor/transitions/src")""",
    "Core framework": r"""(File_dirname = "./src/Spec"
    OR File_dirname = "./src/CSL"
    OR File_basename = "Lib.v")""",
    "Armada total": r"""(File_dirname = "./vendor/transitions/src"
    OR File_dirname = "./src/Spec"
    OR File_dirname = "./src/CSL"
    OR File_basename = "Lib.v")""",
    "Go semantics": r"""(File_dirname = "./src/Goose/Proof")""",
    "Single-disk semantics": r"""(File_dirname = "./src/Examples/ExMach")""",
    "Microbenchmark examples": r"""(File_dirname glob "./src/Examples/*"
    AND NOT File_dirname = "./src/Examples/MailServer"
    AND NOT File_dirname = "./src/Examples/ExMach"
    AND NOT File_dirname = "./src/Examples/ReplicatedDisk")""",
    "Write-ahead logging": r"""(File_dirname = "./src/Examples/AtomicPair"
AND File_basename glob "*Log*")""",
    "Shadow copy": r"""(File_dirname = "./src/Examples/AtomicPair"
AND File_basename glob "*Shadow*")""",
    "Group commit": r"""(File_dirname = "./src/Examples/Logging")""",
    "Two-disk semantics": r"""(File_dirname = "./src/Examples/ReplicatedDisk"
AND (File_basename = "OneDiskAPI.v" OR
     File_basename = "WeakestPre.v" OR
     File_basename = "RefinementAdequacy.v"))""",
    "Replicated disk": r"""(File_dirname = "./src/Examples/ReplicatedDisk"
AND NOT (File_basename = "OneDiskAPI.v" OR
         File_basename = "WeakestPre.v" OR
         File_basename = "RefinementAdequacy.v"))""",
    "Mailboat proof": r"""(File_dirname = "./src/Examples/MailServer")""",
}

goose_where = r"""(NOT File_basename glob "*_test.go"
AND (File_dirname = "." OR
File_dirname = "./internal/coq" OR
File_dirname = "./cmd/goose"))"""

goose_libs = r"""(NOT File_basename glob "*_test.go"
AND File_dirname glob "./machine*"
AND NOT File_basename = "mem.go")"""


def header(s):
    print("\033[1;37m{}\033[0m".format(s))


def round10(n):
    if n is None:
        return 0
    return round(n, -1)


def add_commas(n):
    return "\\loc{}".format("{" + str(n) + "}")


def format_loc(loc):
    return add_commas(round10(loc))


class LatexOutput:
    def __init__(self, db, file):
        self.db = db
        self.file = file

    def line(self, s):
        print(s, file=self.file)

    def loc(self, name, loc, bold=False):
        loc_latex = format_loc(loc)
        name_latex = "\\textbf{" + name + "}" if bold else name
        self.line("{} & {} \\\\".format(name_latex, loc_latex))

    def row(self, name, bold=False):
        loc = self.db.loc(collections[name])
        self.loc(name, loc, bold)

    def bold(self, name):
        self.row(name, bold=True)

    def sep(self):
        self.line("\\midrule")

    def table_start(self, colspec):
        self.line(r"""\begin{tabular}{""" + colspec + "}")
        self.line(r"""\toprule""")

    def table_end(self):
        self.line(r"""\bottomrule""")
        self.line(r"""\end{tabular}{}""")


def debug_counts(db, where):
    loc = db.loc(where)
    file_counts = db.files(where)
    print("LOC   =", round10(loc))
    print("files =", len(file_counts))
    for filename, floc in file_counts:
        print("{:4} {}".format(floc, filename))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--debug", action="store_true", help="print more detailed file information"
    )
    parser.add_argument("src", help="path to Armada source")
    parser.add_argument("goose", help="path to goose source")

    args = parser.parse_args()

    db = LineCountDb.count_lines(args.src)
    goose_db = LineCountDb.count_lines(args.goose)

    if args.debug:
        for name, where in collections.items():
            header(name)
            debug_counts(db, where)
        header("Goose")
        debug_counts(goose_db, goose_where)
        header("Goose library")
        debug_counts(goose_db, goose_libs)
    else:
        with open("impl-loc.tex", "w") as f:
            output = LatexOutput(db, f)
            output.line("% auto-generated by loc.py")
            output.table_start("lr")
            output.line(r"""\bf Component & \bf Lines of code \\""")
            output.sep()
            output.row("Transition system DSL")
            output.row("Core framework")
            output.bold("Armada total")
            output.sep()
            output.loc("Goose translator (Go)", goose_db.loc(goose_where))
            output.loc("Goose library (Go)", goose_db.loc(goose_libs))
            output.row("Go semantics")
            # output.sep()
            # # TODO: get this from the mailboat source code
            # output.loc("Mailboat code (Go)", 159)
            # output.row("Mailboat proof")
            output.table_end()

        with open("examples-loc.tex", "w") as f:
            output = LatexOutput(db, f)
            output.line("% auto-generated by loc.py")
            output.table_start("lr")
            output.line(r"""\bf Example & \bf Lines of code \\""")
            output.sep()
            output.row("Two-disk semantics")
            output.row("Replicated disk")
            output.sep()
            output.row("Single-disk semantics")
            output.row("Write-ahead logging")
            output.row("Shadow copy")
            output.row("Group commit")
            output.table_end()
