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
        "--skip-goose-examples",
        help="skip translating examples in Goose",
        action="store_true",
    )
    parser.add_argument(
        "--nfsd",
        help="path to goose-nfsd repo (skip translation if not provided)",
        metavar="GOOSE_NFSD_PATH",
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
        "--gokv",
        help="path to gokv repo (skip translation if not provided)",
        metavar="GOKV_PATH",
        default=None,
    )

    args = parser.parse_args()

    goose_dir = args.goose
    goose_nfsd_dir = args.nfsd
    journal_dir = args.journal
    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "..")
    examples_dir = args.examples
    distributed_dir = args.distributed_examples
    gokv_dir = args.gokv
    marshal_dir = args.marshal

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if goose_nfsd_dir is not None and not os.path.isdir(goose_nfsd_dir):
        parser.error("goose-nfsd directory does not exist")
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
    if marshal_dir is not None and not os.path.isdir(marshal_dir):
        parser.error("marshal directory does not exist")

    # Goose is not module-aware, so we revert to the pre-1.16 behavior of
    # detecting whether to use modules or not.
    if not args.dry_run:
        os.environ["GO111MODULE"] = "auto"
    if args.dry_run or args.verbose:
        print("set GO111MODULE=auto")

    do_run = lambda cmd_args: run_command(
        cmd_args, dry_run=args.dry_run, verbose=args.verbose
    )

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        os.chdir(old_dir)

    def run_goose(src_path, output, pkg=None, ffi=None, excludes=None):
        if excludes is None:
            excludes = []
        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose")
        args = [goose_bin, "-out", output]
        if pkg is not None:
            args.extend(["-package", pkg])
        if ffi is not None:
            args.extend(["-ffi", ffi])
        for e in excludes:
            args.extend(["-exclude-import", e])
        args.append(src_path)
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
        for example in [
            "unittest",
            "semantics",
            "append_log",
            "logging2",
            "rfc1813",
            "simpledb",
            "wal",
        ]:
            run_goose(
                path.join(goose_dir, "internal/examples/", example),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/tchajed/goose/internal/examples/" + example,
            )

    if journal_dir is not None:
        pkgs = [
            "addr",
            "alloc",
            "buf",
            "jrnl",
            "common",
            "lockmap",
            "obj",
            "util",
            "wal",
            "jrnl_replication",
            "txn",
        ]
        for pkg in pkgs:
            run_goose(
                path.join(journal_dir, pkg),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/mit-pdos/go-journal/" + pkg,
            )

    if goose_nfsd_dir is not None:
        pkgs = [
            "kvs",
            "super",
            "fh",
            "simple",
        ]
        for pkg in pkgs:
            run_goose(
                path.join(goose_nfsd_dir, pkg),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/mit-pdos/goose-nfsd/" + pkg,
            )
        # the workaround here is to have a directory nfstypes that only has
        # nfs_types.go and not nfs_xdr.go (Goose doesn't support excluding some
        # files)
        run_goose(
            path.join(goose_nfsd_dir, "nfstypes/goose-workaround/nfstypes"),
            path.join(perennial_dir, "external/Goose"),
            pkg="github.com/mit-pdos/goose-nfsd/nfstypes",
        )

    if examples_dir is not None:
        pkgs = [
            "replicated_block",
            "alloc",
            "inode",
            "indirect_inode",
            "async_inode",
            "dir",
            "dynamic_dir",
            "single_inode",
            "single_async_inode",
            "toy",
        ]
        for pkg in pkgs:
            run_goose(
                path.join(examples_dir, pkg),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/mit-pdos/perennial-examples/" + pkg,
            )

    if distributed_dir is not None:
        pkgs = ["grove_common", "."]
        for pkg in pkgs:
            if pkg == ".":
                run_goose(
                    path.join(distributed_dir),
                    path.join(perennial_dir, "external/Goose"),
                    pkg="github.com/mit-pdos/lockservice/",
                    import_header="From Perennial.goose_lang Require Import ffi.grove_prelude.",
                    excludes=["github.com/mit-pdos/lockservice/grove_ffi"],
                )
            else:
                run_goose(
                    path.join(distributed_dir, pkg),
                    path.join(perennial_dir, "external/Goose"),
                    pkg="github.com/mit-pdos/lockservice/" + pkg,
                    import_header="From Perennial.goose_lang Require Import ffi.grove_prelude.",
                    excludes=["github.com/mit-pdos/lockservice/grove_ffi"],
                )

    if gokv_dir is not None:
        pkgs = ["urpc/rpc", "memkv", "paxi/single"]

        for pkg in pkgs:
            run_goose(
                path.join(gokv_dir, pkg),
                path.join(perennial_dir, "external/Goose"),
                pkg="github.com/mit-pdos/gokv/" + pkg,
                ffi="dist",
                excludes=[
                    "github.com/mit-pdos/gokv/dist_ffi",
                ]
                # XXX: need to change the Coq import statement for lockservice/ from
                # "From Goose Require github_com.mit_pdos.lockservice.lockservice." to
                # "From Goose Require github_com.mit_pdos.lockservice."
            )

    if marshal_dir is not None:
        run_goose(
            marshal_dir,
            path.join(perennial_dir, "external/Goose"),
            pkg="github.com/tchajed/marshal",
            ffi="none",
        )


if __name__ == "__main__":
    main()
