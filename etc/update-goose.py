#!/usr/bin/env python3

import os
import subprocess
from os import path


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
        "--models",
        help="translate goose models (e.g., channels and strings)",
        action="store_true",
    )
    parser.add_argument(
        "--examples",
        help="path to perennial-examples repo (skip translation if not provided)",
        metavar="PERENNIAL_EXAMPLES_PATH",
        default=None,
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

    args = parser.parse_args()

    goose_dir = args.goose
    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "..")
    examples_dir = args.examples
    marshal_dir = args.marshal
    std_dir = args.std

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if examples_dir is not None and not os.path.isdir(examples_dir):
        parser.error("perennial-examples directory does not exist")
    if marshal_dir is not None and not os.path.isdir(marshal_dir):
        parser.error("marshal directory does not exist")
    if std_dir is not None and not os.path.isdir(std_dir):
        parser.error("std directory does not exist")

    def do_run(cmd_args):
        run_command(cmd_args, dry_run=args.dry_run, verbose=args.verbose)

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        os.chdir(old_dir)

    def run_goose(src_path, *pkgs, extra_args=None):
        if src_path is None:
            return
        if not pkgs:
            pkgs = ["."]
        if not extra_args:
            extra_args = []

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose")
        args = [goose_bin]

        output = path.join(perennial_dir, "external/Goose")
        args.extend(["-out", output])
        args.extend(["-dir", src_path])
        args.extend(extra_args)
        args.extend(pkgs)
        do_run(args)

    if args.compile:
        compile_goose()

    if args.models:
        run_goose(goose_dir, "./channel")
        run_goose(goose_dir, "./strings")

    if args.goose_examples:
        # generate semantics tests
        src_path = path.join(goose_dir, "internal/examples/semantics")
        output = path.join(perennial_dir, "src/goose_lang/interpreter/generated_test.v")
        gen_bin = path.join(goose_dir, "cmd/test_gen/main.go")
        do_run(["go", "run", gen_bin, "-coq", "-out", output, src_path])

        run_goose(
            path.join(goose_dir, "internal/examples"),
            "./append_log",
            "./async",
            "./comments",
            "./logging2",
            "./rfc1813",
            "./semantics",
            "./simpledb",
            "./trust_import/...",
            "./unittest/...",
            "./wal",
        )

    run_goose(
        examples_dir,
        "./replicated_block",
        "./alloc",
        "./inode",
        "./indirect_inode",
        "./async_inode",
        "./dir",
        "./dynamic_dir",
        "./single_inode",
        "./single_async_inode",
        "./toy",
        "./async_toy",
        "./async_durable_alloc_inode",
        "./async_mem_alloc_inode",
        "./async_mem_alloc_dir",
        "./async_durable_alloc",
    )

    run_goose(marshal_dir, ".", extra_args=["-skip-interfaces"])

    run_goose(std_dir, "./...")


if __name__ == "__main__":
    main()
