#!/usr/bin/env python3

import os
from os import path
import subprocess


def run_command(args, dry_run=False, verbose=False):
    if dry_run or verbose:
        print(" ".join(args))
    if not dry_run:
        subprocess.run(args, check=True)


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Update goose output")
    parser.add_argument(
        "--compile", help="also compile and install goose", action="store_true"
    )
    parser.add_argument(
        "-n",
        "--dry-run",
        help="print commands without running them",
        action="store_true",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        help="print commands in addition to running them",
        action="store_true",
    )
    parser.add_argument(
        "--goose",
        help="path to goose repo",
        required=True,
        metavar="GOOSE_PATH",
    )
    parser.add_argument(
        "--goose-examples",
        help="also translate tests in Goose",
        action="store_true",
    )
    parser.add_argument(
        "--marshal",
        help="path to marshal repo (skip translation if not provided)",
        metavar="MARSHAL_PATH",
        default=None,
    )
    parser.add_argument(
        "--std",
        help="path to goose-lang/std repo (skip translation if not provided)",
        metavar="STD_PATH",
        default=None,
    )
    parser.add_argument(
        "--gokv",
        help="path to gokv repo (skip translation if not provided)",
        metavar="GOKV_PATH",
        default=None,
    )

    args = parser.parse_args()

    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "../..")
    goose_dir = args.goose
    marshal_dir = args.marshal
    std_dir = args.std
    gokv_dir = args.gokv

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if marshal_dir is not None and not os.path.isdir(marshal_dir):
        parser.error("marshal directory does not exist")
    if std_dir is not None and not os.path.isdir(std_dir):
        parser.error("std directory does not exist")
    if gokv_dir is not None and not os.path.isdir(gokv_dir):
        parser.error("gokv directory does not exist")

    do_run = lambda cmd_args: run_command(
        cmd_args, dry_run=args.dry_run, verbose=args.verbose
    )

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        os.chdir(old_dir)

    def run_goose(src_path, *pkgs):
        if src_path is None:
            return
        if not pkgs:
            pkgs = ["."]

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose")
        args = [goose_bin]

        output = path.join(perennial_dir, "new/code/")
        args.extend(["-out", output])
        args.extend(["-dir", src_path])
        args.extend(pkgs)
        do_run(args)

    def run_goose_test_gen(src_path, output):
        gen_bin = path.join(goose_dir, "cmd/test_gen/main.go")
        args = ["go", "run", gen_bin, "-coq", "-out", output, src_path]
        do_run(args)

    if args.compile:
        compile_goose()

    if args.goose_examples:
        run_goose(
            path.join(goose_dir, "testdata/examples"),
            "./append_log",
        )

    run_goose(marshal_dir, ".")

    run_goose(std_dir, ".")

    run_goose(
        gokv_dir,
        "./urpc",
        "./reconnectclient",
        "./asyncfile",
        "./vrsm/paxos",
        # "./vrsm/replica",
    )


if __name__ == "__main__":
    main()
