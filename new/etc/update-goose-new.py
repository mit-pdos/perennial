#!/usr/bin/env python3

import os
from os import path
import subprocess
import sys

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
            "./trusted_proph",
            "./globals_test",
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
    create_proj(repo="mit-pdos/go-journal"),
    create_proj(
        repo="sanjit-bhat/pav",
        pkgs=[
            "./advrpc",
            "./alicebob",
            "./auditor",
            "./client",
            "./cryptoffi",
            "./cryptoutil",
            "./hashchain",
            "./ktcore",
            "./merkle",
            "./netffi",
            "./safemarshal",
            "./server",
        ],
    ),
]


class ProcessManager:
    def __init__(self, dry_run=None, verbose=None, max_procs=1):
        self._processes = []
        self._dry_run = dry_run
        self._verbose = verbose
        self._max_procs = max_procs
        # the last non-zero exit code
        self._failed_status = None

    def run_command(self, args):
        if self._dry_run or self._verbose:
            print(" ".join(args))
        if not self._dry_run:
            self._processes.append(subprocess.Popen(args, stderr=subprocess.PIPE))
        else:
            return None

    def _wait1(self):
        if self._processes:
            p = self._processes.pop()
            stdout_bytes, stderr_bytes = p.communicate()
            sys.stderr.buffer.write(stderr_bytes)
            if p.returncode != 0 and (self._failed_status is not None):
                self._failed_status = p.returncode
                # finish everything running and then exit
                self.wait_all()
                sys.exit(self._failed_status)

    def wait_all(self):
        while self._processes:
            self._wait1()

    # wait if there are too many pending processes
    def check(self):
        while len(self._processes) > self._max_procs:
            self._wait1()


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
        "--channel",
        help="translate channel model",
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
        if proj_dir(proj.name) is not None and not os.path.isdir(proj_dir(proj.name)):
            parser.error(f"{proj.name} directory does not exist")

    if not os.path.isdir(goose_dir):
        parser.error("goose directory does not exist")

    max_procs = os.cpu_count()
    # don't want too many processes since each goose invocation also has some
    # parallelism
    if max_procs and max_procs > 1:
        max_procs = max_procs / 2
    pm = ProcessManager(
        dry_run=args.dry_run,
        verbose=args.verbose,
        max_procs=max_procs,
    )

    def do_run(cmd_args):
        pm.run_command(cmd_args)

    def compile_goose():
        old_dir = os.getcwd()
        os.chdir(goose_dir)
        do_run(["go", "install", "./cmd/goose", "./cmd/proofgen"])
        os.chdir(old_dir)
        pm.wait_all()

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
            [
                goose_bin,
                "-out",
                path.join(perennial_dir, "new/code/"),
                "-dir",
                src_path,
            ]
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

    # NOTE: new goose doesn't have executable tests for now, evaluation is blocked due to sealing
    # def run_goose_test_gen(src_path, output):
    #    gen_bin = path.join(goose_dir, "cmd/test_gen/main.go")
    #    args = ["go", "run", gen_bin, "-coq", "-out", output, src_path]
    #    do_run(args)

    if args.compile:
        compile_goose()

    if args.goose_examples:
        run_goose(
            path.join(goose_dir, "testdata/examples"),
            "./append_log",
            "./semantics",
            "./unittest/...",
            "./channel",
        )

    if args.channel:
        run_goose(goose_dir, "./model/channel")

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
    pm.wait_all()


if __name__ == "__main__":
    main()
