#!/usr/bin/env python

from __future__ import print_function

import argparse
import sqlite3
import pandas

def read_db(fname):
    conn = sqlite3.connect(fname)
    conn.row_factory = sqlite3.Row
    qed_timings = []
    for row in conn.execute("select fname, ident, time from qed_timings"):
        qed_timings.append((row["fname"], row["ident"], row["time"]))

    file_timings = []
    for row in conn.execute(
        """SELECT file_timings.fname as fname, time, qed_time FROM """
        + """(file_timings INNER JOIN """
        + """(SELECT fname, sum(time) AS qed_time FROM qed_timings group by fname) file_qeds """
        + """on file_timings.fname = file_qeds.fname)"""
    ):
        file_timings.append((row["fname"], row["time"], row["qed_time"]))

    conn.close()

    qed_df = pandas.DataFrame(qed_timings, columns=["fname", "ident", "time"])
    file_df = pandas.DataFrame(file_timings, columns=["fname", "time", "qed_time"])
    return qed_df, file_df


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("db", help="sqlite database of timing info")

    args = parser.parse_args()

    qed_df, file_df = read_db(args.db)
    print("{:12s} {:>6.1f}".format("total", file_df["time"].sum()))
    print(
        "{:12s} {:>6.1f}".format(
            " Iris",
            file_df[file_df["fname"].str.contains("^external/iris-coq")]["time"].sum(),
        )
    )
    print(
        "{:12s} {:>6.1f}".format(
            " stdpp",
            file_df[file_df["fname"].str.contains("^external/stdpp")]["time"].sum(),
        )
    )
    print(
        "{:12s} {:>6.1f}".format(
            " vendor", file_df[file_df["fname"].str.contains("^vendor/")]["time"].sum()
        )
    )
    print("{:12s} {:>6.1f}".format("Qed total", file_df["qed_time"].sum()))

    print()
    print("slow files:")
    print(file_df.sort_values("time", ascending=False)[:10])

    print()
    print("slow QEDs:")
    print(qed_df.sort_values("time", ascending=False)[:10])
