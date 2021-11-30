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

    parser = argparse.ArgumentParser(
        description="Update goose output from goose tests and go-nfsd"
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
        "--skip-goose-examples",
        help="skip translating examples in Goose",
        action="store_true",
    )
    parser.add_argument(
        "--nfsd",
        help="path to go-nfsd repo (skip translation if not provided)",
        metavar="GO_NFSD_PATH",
        default=None,
    )
    parser.add_argument(
        "--journal",
        help="path to go-journal repo (skip translation if not provided)",
        metavar="GO_JOURNAL_PATH",
        default=None,
    )
    parser.add_argument(
        "--examples",
        help="path to perennial-examples repo (skip translation if not provided)",
        metavar="PERENNIAL_EXAMPLES_PATH",
        default=None,
    )
    parser.add_argument(
        "--distributed-examples",
        help="path to lockservice repo (skip translation if not provided)",
        metavar="DISTRIBUTED_EXAMPLES_PATH",
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
    parser.add_argument(
        "--gokv",
        help="path to gokv repo (skip translation if not provided)",
        metavar="GOKV_PATH",
        default=None,
    )
    parser.add_argument(
        "--mvcc",
        help="path to go-mvcc repo (skip translation if not provided)",
        metavar="MVCC_PATH",
        default=None,
    )

    args = parser.parse_args()

    goose_dir = args.goose
    go_nfsd_dir = args.nfsd
    journal_dir = args.journal
    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "..")
    examples_dir = args.examples
    distributed_dir = args.distributed_examples
    gokv_dir = args.gokv
    mvcc_dir = args.mvcc
    marshal_dir = args.marshal
    std_dir = args.std

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if go_nfsd_dir is not None and not os.path.isdir(go_nfsd_dir):
        parser.error("go-nfsd directory does not exist")
    if journal_dir is not None and not os.path.isdir(journal_dir):
        parser.error("go-journal directory does not exist")
    if examples_dir is not None and not os.path.isdir(examples_dir):
        parser.error("perennial-examples directory does not exist")
    if distributed_dir is not None and not os.path.isdir(distributed_dir):
        parser.error(
            "lockservice (distributed examples) directory does not exist"
        )
    if gokv_dir is not None and not os.path.isdir(gokv_dir):
        parser.error("gokv directory does not exist")
    if mvcc_dir is not None and not os.path.isdir(mvcc_dir):
        parser.error("mvcc directory does not exist")
    if marshal_dir is not None and not os.path.isdir(marshal_dir):
        parser.error("marshal directory does not exist")
    if std_dir is not None and not os.path.isdir(std_dir):
        parser.error("std directory does not exist")

    do_run = lambda cmd_args: run_command(
        cmd_args, dry_run=args.dry_run, verbose=args.verbose
    )

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        os.chdir(old_dir)

    def run_goose(src_path, *pkgs):
        if not pkgs:
            pkgs = ["."]

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose")
        args = [goose_bin]

        output = path.join(perennial_dir, "external/Goose")
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

    if not args.skip_goose_examples:
        run_goose_test_gen(
            path.join(goose_dir, "internal/examples/semantics"),
            path.join(
                perennial_dir, "src/goose_lang/interpreter/generated_test.v"
            ),
        )
        run_goose(
            path.join(goose_dir, "internal/examples"),
            "./unittest",
            "./semantics",
            "./append_log",
            "./logging2",
            "./rfc1813",
            "./simpledb",
            "./wal",
        )

    if journal_dir is not None:
        run_goose(
            journal_dir,
            "./addr",
            "./alloc",
            "./buf",
            "./jrnl",
            "./common",
            "./lockmap",
            "./obj",
            "./util",
            "./wal",
            "./jrnl_replication",
            "./txn",
        )

    if go_nfsd_dir is not None:
        run_goose(
            go_nfsd_dir,
            "./kvs",
            "./super",
            "./fh",
            "./simple",
            "./nfstypes",
        )

    if examples_dir is not None:
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

    if distributed_dir is not None:
        run_goose(distributed_dir, ".", "./grove_common")

    if gokv_dir is not None:
        pkgs = ["urpc/rpc", "memkv", "connman", "paxi/single", "bank", "lockservice", "pb", "pb/controller"]

        for pkg in pkgs:
            run_goose(
                path.join(gokv_dir, pkg),
                # XXX: need to change the Coq import statement for lockservice/ from
                # "From Goose Require github_com.mit_pdos.lockservice.lockservice." to
                # "From Goose Require github_com.mit_pdos.lockservice."
            )

    if mvcc_dir is not None:
        run_goose(
            mvcc_dir,
            "./txn",
            "./index",
            "./gc",
            "./tuple",
			"./config",
			# "./cfmutex",
        )

    if marshal_dir is not None:
        run_goose(marshal_dir, ".")

    if std_dir is not None:
        run_goose(std_dir, ".")


if __name__ == "__main__":
    main()
