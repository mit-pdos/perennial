#!/usr/bin/env python3

import os
from os import path
import subprocess

from dataclasses import dataclass


@dataclass
class Proj:
    name: str
    repo: str
    pkgs: list[str]


def create_proj(name=None, repo=None, pkgs=None):
    if name is None:
        name = repo.split("/")[-1]
    if pkgs is None:
        pkgs = ["./..."]
    return Proj(name, repo, pkgs)


# define the supported projects
projs = [
    create_proj(repo="goose-lang/std"),
    create_proj(repo="tchajed/marshal"),
    create_proj(repo="goose-lang/primitive", pkgs=[".", "./disk"]),
    create_proj(
        repo="mit-pdos/gokv",
        pkgs=[
            "./partialapp",
            "./asyncfile",
            "./urpc",
            "./kv",
            "./bank",
            "./lockservice",
            "./map_string_marshal",
            "./vrsm/replica",
            "./vrsm/reconfig",
            "./vrsm/configservice",
            "./vrsm/apps/exactlyonce",
            "./vrsm/apps/vkv",
            "./vrsm/paxos",
            "./aof",
            "./reconnectclient",
            "./vrsm/e",
            "./vrsm/clerk",
            "./vrsm/storage",
            "./vrsm/apps/closed",
            "./map_marshal",
            "./cachekv",
            "./trusted_proph"
        ],
    ),
    create_proj(
        repo="upamanyus/etcd-raft",
        pkgs=[
            ".",
            "github.com/stretchr/testify/assert",
            "go.etcd.io/raft/v3/confchange",
            "go.etcd.io/raft/v3/quorum",
            "go.etcd.io/raft/v3/quorum/slices",
            "go.etcd.io/raft/v3/raftpb",
            "go.etcd.io/raft/v3/tracker",
        ],
    ),
    create_proj(
        repo="upamanyus/etcd",
        pkgs=[
            "time",
            "math",
            "google.golang.org/grpc",
            "go.etcd.io/etcd/api/v3/etcdserverpb",
            "go.etcd.io/etcd/api/v3/mvccpb",
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/client/v3/concurrency",
            "go.etcd.io/etcd/client/v3/leasing",
            "go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
            "google.golang.org/grpc/codes",
            "google.golang.org/grpc/status",
            "go.uber.org/zap",
            "go.uber.org/zap/zapcore",
        ],
    ),
]


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
        "--std-lib",
        help="translate (parts of) Go standard library",
        action="store_true",
    )
    for proj in projs:
        parser.add_argument(
            f"--{proj.name}",
            help=f"path to {proj.repo} repo (skip translation if not provided)",
            metavar=f"{proj.name.upper()}_PATH",
            default=None,
        )

    args = parser.parse_args()

    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "../..")
    goose_dir = args.goose

    def proj_dir(name):
        return getattr(args, name.replace("-", "_"))

    for proj in projs:
        if not os.path.isdir(proj_dir(proj.name)):
            parser.error(f"{proj.name} directory does not exist")

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")

    def do_run(cmd_args):
        run_command(cmd_args, dry_run=args.dry_run, verbose=args.verbose)

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose"])
        do_run(["go", "install", "./cmd/proofgen"])
        os.chdir(old_dir)

    def run_goose(src_path, *pkgs, extra_args=None):
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
        do_run(
            [goose_bin, "-out", path.join(perennial_dir, "new/code/"), "-dir", src_path]
            + pkgs
        )

        proofgen_bin = path.join(gopath, "bin", "proofgen")

        do_run(
            [
                proofgen_bin,
                "-out",
                path.join(perennial_dir, "new/generatedproof"),
                "-configdir",
                path.join(perennial_dir, "new/code"),
                "-dir",
                src_path,
            ]
            + pkgs
        )

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

    if args.std_lib:
        # this list of packages comes from the dependencies of etcd-raft
        run_goose(
            goose_dir,
            "testing",
            "bytes",
            "context",
            "crypto/rand",
            "errors",
            "io",
            "math",
            "math/big",
            "math/rand",
            "os",
            "sort",
            "slices",
            "strconv",
            "strings",
            "sync",
            "sync/atomic",
            "internal/race",
            "fmt",
            "log",
        )

    for proj in projs:
        run_goose(
            proj_dir(proj.name),
            *proj.pkgs,
        )


if __name__ == "__main__":
    main()
