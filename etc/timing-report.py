#!/usr/bin/env python3

from __future__ import print_function

import sqlite3
import pandas as pd


def read_db(fname):
    conn = sqlite3.connect(fname)
    conn.row_factory = sqlite3.Row
    qed_timings = []
    for row in conn.execute("SELECT fname, ident, time FROM qed_timings"):
        qed_timings.append((row["fname"], row["ident"], row["time"]))

    file_timings = []
    for row in conn.execute("""SELECT fname, time FROM file_timings"""):
        file_timings.append((row["fname"], row["time"]))
    conn.close()

    qed_df = pd.DataFrame(qed_timings, columns=["fname", "ident", "time"])
    qed_sum = qed_df.groupby("fname").sum()
    raw_file_df = pd.DataFrame(file_timings, columns=["fname", "time"])
    file_df = raw_file_df.join(qed_sum, rsuffix="_qed", on="fname")
    file_df.rename(mapper={"time_qed": "qed_time"}, axis="columns", inplace=True)
    file_df.fillna(value={"qed_time": 0.0}, inplace=True)
    return qed_df, file_df


def filter_df(df, col=None, pat=None):
    return df[df[col].str.contains(pat)]


if __name__ == "__main__":
    import argparse
    import os.path
    import sys

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--max", type=int, default=10, help="number of slowest files and proofs to show"
    )
    parser.add_argument("--db",
            help="sqlite database of timing info",
            default=".timing.sqlite3")

    args = parser.parse_args()

    if not os.path.exists(args.db):
        print("database file {} not found".format(args.db), file=sys.stderr)
        sys.exit(1)
    qed_df, file_df = read_db(args.db)
    pd.set_option("display.max_rows", 100)
    pd.set_option("display.max_columns", 10)
    pd.set_option("display.width", 300)
    print("{:12s} {:>6.1f}".format("total", file_df["time"].sum()))
    print(
        "{:12s} {:>6.1f}".format(
            " Iris",
            filter_df(file_df, col="fname", pat="^external/iris-coq")["time"].sum(),
        )
    )
    print(
        "{:12s} {:>6.1f}".format(
            " stdpp",
            filter_df(file_df, col="fname", pat="^external/stdpp")["time"].sum(),
        )
    )
    print("{:12s} {:>6.1f}".format("Qed total", file_df["qed_time"].sum()))

    if args.max > 0:
        print()
        print("slow files:")
        print(file_df.nlargest(args.max, "time"))

        if len(qed_df) > 0:
            print()
            print("slow QEDs:")
            print(qed_df.nlargest(args.max, "time"))
