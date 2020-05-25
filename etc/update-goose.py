#!/usr/bin/env python3

import os
from os import path
import subprocess


def run_command(args, dry_run=False, verbose=False):
    if dry_run or verbose:
        print(" ".join(args))
    if not dry_run:
        subprocess.run(args)


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Update goose output from goose tests and goose-nfsd"
    )
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
        "--nfsd",
        help="path to goose-nfsd repo (skip translation if not provided)",
        metavar="GOOSE_NFSD_PATH",
        default=None,
    )
    parser.add_argument(
        "--examples",
        help="path to perennial-examples repo (skip translation if not provided)",
        metavar="PERENNIAL_EXAMPLES_PATH",
        default=None,
    )

    args = parser.parse_args()

    goose_dir = args.goose
    goose_nfsd_dir = args.nfsd
    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "..")
    examples_dir = args.examples

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if goose_nfsd_dir is not None and not os.path.isdir(goose_nfsd_dir):
        parser.error("goose-nfsd directory does not exist")
    if examples_dir is not None and not os.path.isdir(examples_dir):
        parser.error("perennial-examples directory does not exist")

    do_run = lambda cmd_args: run_command(
        cmd_args, dry_run=args.dry_run, verbose=args.verbose
    )

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        os.chdir(old_dir)

    def run_goose(src_path, output, pkg=None):
        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose")
        args = [goose_bin, "-out", output]
        if pkg is not None:
            args.extend(["-package", pkg])
        args.append(src_path)
        do_run(args)

    def run_goose_test_gen(src_path, output):
        gen_bin = path.join(goose_dir, "cmd/test_gen/main.go")
        args = ["go", "run", gen_bin, "-coq", "-out", output, src_path]
        do_run(args)

    if args.compile:
        compile_goose()

    run_goose(
        path.join(goose_dir, "internal/examples/unittest"),
        path.join(perennial_dir, "src/goose_lang/examples/goose_unittest.v"),
    )
    run_goose(
        path.join(goose_dir, "internal/examples/semantics"),
        path.join(perennial_dir, "src/goose_lang/examples/goose_semantics.v"),
    )
    run_goose_test_gen(
        path.join(goose_dir, "internal/examples/semantics"),
        path.join(perennial_dir, "src/goose_lang/interpreter/generated_test.v"),
    )
    for example in ["append_log", "logging2", "rfc1813", "simpledb", "wal"]:
        run_goose(
            path.join(goose_dir, "internal/examples/", example),
            path.join(
                perennial_dir, "src/goose_lang/examples/", example + ".v"
            ),
        )

    if goose_nfsd_dir is not None:
        pkgs = [
            "addr",
            "alloc",
            "buf",
            "buftxn",
            "common",
            "kvs",
            "lockmap",
            "super",
            "txn",
            "util",
            "wal",
        ]
        for pkg in pkgs:
            if pkg == ".":
                run_goose(
                    goose_nfsd_dir,
                    path.join(perennial_dir, "external/Goose"),
                    pkg="github.com/mit-pdos/goose-nfsd",
                )
            else:
                run_goose(
                    path.join(goose_nfsd_dir, pkg),
                    path.join(perennial_dir, "external/Goose"),
                    pkg="github.com/mit-pdos/goose-nfsd/" + pkg,
                )
    if examples_dir is not None:
        pkgs = [
            "alloc",
            "inode",
            "indirect_inode",
            "dir",
        ]
        for pkg in pkgs:
            run_goose(
                path.join(examples_dir, pkg),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/mit-pdos/perennial-examples/" + pkg,
            )


if __name__ == "__main__":
    main()
