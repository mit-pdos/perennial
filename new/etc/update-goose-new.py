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
        "--etcd-raft",
        help="path to upamanyus/etcd-raft repo (skip translation if not provided)",
        metavar="ETCD_RAFT_PATH",
        default=None,
    )

    args = parser.parse_args()

    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "../..")
    goose_dir = args.goose
    std_dir = args.std
    gokv_dir = args.gokv
    etcd_raft_dir = args.etcd_raft

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")
    if std_dir is not None and not os.path.isdir(std_dir):
        parser.error("std directory does not exist")
    if gokv_dir is not None and not os.path.isdir(gokv_dir):
        parser.error("gokv directory does not exist")
    if etcd_raft_dir is not None and not os.path.isdir(etcd_raft_dir):
        parser.error("etcd-raft directory does not exist")

    def do_run(cmd_args):
        run_command(cmd_args, dry_run=args.dry_run, verbose=args.verbose)

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        do_run(["go", "install", "./cmd/goose_axiom"])
        do_run(["go", "install", "./cmd/recordgen"])
        do_run(["go", "install", "./cmd/namegen"])
        os.chdir(old_dir)

    def run_goose(src_path, *pkgs):
        if src_path is None:
            return
        if not pkgs:
            pkgs = ["."]
        else:
            pkgs = list(pkgs)

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")

        goose_bin = path.join(gopath, "bin", "goose")
        do_run([goose_bin,
                "-out", path.join(perennial_dir, "new/code/"),
                "-dir", src_path] + pkgs)

        recordgen_bin = path.join(gopath, "bin", "recordgen")
        do_run([recordgen_bin,
                "-out", path.join(perennial_dir, "new/generatedproof/structs"),
                "-dir", src_path] + pkgs)

        namegen_bin = path.join(gopath, "bin", "namegen")
        do_run([namegen_bin,
                "-out", path.join(perennial_dir, "new/generatedproof/names"),
                "-dir", src_path] + pkgs)

    def run_recordgen(src_path, *pkgs):
        if src_path is None:
            return
        if not pkgs:
            pkgs = ["."]
        else:
            pkgs = list(pkgs)

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")

        recordgen_bin = path.join(gopath, "bin", "recordgen")
        do_run([recordgen_bin,
                "-out", path.join(perennial_dir, "new/generatedproof/structs"),
                "-dir", src_path] + pkgs)

    def run_axiomgen(dst_path, src_path, *pkgs):
        if src_path is None:
            return
        if not pkgs:
            pkgs = ["."]

        gopath = os.getenv("GOPATH", default=None)
        if gopath is None or gopath == "":
            gopath = path.join(path.expanduser("~"), "go")
        goose_bin = path.join(gopath, "bin", "goose_axiom")
        args = [goose_bin]

        output = path.join(perennial_dir, dst_path)
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
            "./semantics",
            "./unittest",
        )

    run_goose(std_dir, ".")

    run_goose(
        gokv_dir,
        "./urpc",
        "./reconnectclient",
        "./asyncfile",
        "./vrsm/paxos",
        "./kv",
        "./cachekv",
        "./lockservice",
        "./bank",
        "./globals_test",
        # "./vrsm/replica",
    )

    run_axiomgen(
        "new_code_axioms/",
        etcd_raft_dir,
        "testing",
        "bytes",
        "context",
        "crypto/rand",
        "errors",
        "go.etcd.io/raft/v3/confchange",
        "go.etcd.io/raft/v3/quorum/slices64",
        "github.com/stretchr/testify/assert",
        "io",
        "math",
        "math/big",
        "math/rand",
        "os",
        "sort",
        "slices",
        "strconv",
        "strings",
    )

    run_axiomgen(
        "new_partial_axioms/",
        etcd_raft_dir,
        "fmt",
        "log",
        "go.etcd.io/raft/v3/raftpb",
    )

    run_goose(
        etcd_raft_dir,
        ".",
        "go.etcd.io/raft/v3/tracker",
        "go.etcd.io/raft/v3/quorum",
    )

    run_recordgen(
        etcd_raft_dir,
        "go.etcd.io/raft/v3/raftpb",
    )

if __name__ == "__main__":
    main()
