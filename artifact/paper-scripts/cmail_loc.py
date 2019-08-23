#!/usr/bin/env python3
#
# when run, prints out aggregate lines of code from the CSPEC lines of code
# table

import pandas as pd
from io import StringIO


def get_data():
    cspec_table = """
    layer                   spec    code    proof
    MailServerComposed      78      11      65
    MailServerPerUser       129     0       51
    MailServerLockAbs       63      34      470
    Mailbox                 138     0       70
    MailboxTmpAbs           93      25      261
    Deliver                 173     34      204
    DeliverListPid          181     27      106
    MailFS                  146     0       172
    MailFSStringAbs         166     36      128
    MailFSString            145     0       302
    MailFSPathAbs           200     17      72
    MailFSPath              138     31      579
    MailFSMerged            323     0       0
    """

    df = pd.read_csv(StringIO(cspec_table), sep="\s+")
    return df


def sum_lines(df):
    return {
        # the specifications for the intermediate layers in CSPEC are really
        # details of the proof, but the topmost spec is the CMAIL specification
        # and the bottommost spec has all the assumptions about primitive
        # operations (eg, the file system).
        "proof": df["spec"][1:-1].sum() + df["proof"].sum(),
        "code": df["code"].sum(),
    }


def main():
    df = get_data()
    print("Figure 18 table:")
    print(df)
    print()

    results = sum_lines(df)
    # total from Figure 14
    cspec_lines = 9580
    code_lines = results["code"]
    proof_lines = results["proof"]
    print(f"CMAIL code lines: {code_lines})")
    print(f"CMAIL proof lines: {proof_lines} (≈ {round(proof_lines, -1)})")
    print(f"CSPEC framework lines: {cspec_lines} (≈ {round(cspec_lines, -1)})")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        usage="""
cmail_loc.py [-h]

Processes data from the CSPEC paper,
https://pdos.csail.mit.edu/papers/cspec.pdf.

CMAIL numbers come from Figure 18. The CSPEC framework lines of code total is
from Figure 14.
        """.strip()
    )
    args = parser.parse_args()
    main()
