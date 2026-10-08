#!/usr/bin/env python3

import os
import subprocess
import sys
from dataclasses import dataclass
from os import path


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
    create_proj(repo="mit-pdos/go-liveness"),
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
        "-a",
        "--all",
        help="translate all code, assuming it is found in `<ALL>/<proj_name>`",
        metavar="ALL_PATH",
        nargs="?",
        const="..",
    )
    parser.add_argument(
        "--lean",
        help="emit Lean (Perennial/Code, Perennial/GeneratedProof) rather than Rocq (new/code, new/generatedproof)",
        action="store_true",
    )
    parser.add_argument(
        "--goose-examples",
        help="also translate tests in Goose",
        action="store_true",
    )
    parser.add_argument(
        "--models",
        help="translate Go models (e.g., channels and strings)",
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

    if args.all:
        setattr(args, "std_lib", True)
        setattr(args, "models", True)
        setattr(args, "goose_examples", True)
        for proj in projs:
            proj_path = path.join(args.all, proj.name)
            proj_arg = proj.name.replace("-", "_")
            if getattr(args, proj_arg, None) is None and os.path.isdir(proj_path):
                setattr(args, proj_arg, proj_path)

    # this script lives in etc/ (on master: new/etc/)
    perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "..")
    if not os.path.isdir(path.join(perennial_dir, "goose")):
        perennial_dir = path.join(path.dirname(os.path.realpath(__file__)), "../..")
    if args.lean:
        code_dir = path.join(perennial_dir, "Perennial/Code")
        proof_dir = path.join(perennial_dir, "Perennial/GeneratedProof")
        lean_args = ["-lean"]
    else:
        code_dir = path.join(perennial_dir, "new/code/")
        proof_dir = path.join(perennial_dir, "new/generatedproof")
        lean_args = []
    goose_dir = path.join(perennial_dir, "goose")

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
        os.chdir(perennial_dir)
        do_run(["go", "install", "./goose/cmd/goose", "./goose/cmd/proofgen"])
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
            [goose_bin]
            + lean_args
            + [
                "-out",
                code_dir,
                "-configdir",
                code_dir,
                "-dir",
                src_path,
            ]
            + pkgs
        )

        proofgen_bin = path.join(gopath, "bin", "proofgen")

        do_run(
            [proofgen_bin]
            + lean_args
            + [
                "-out",
                proof_dir,
                "-configdir",
                code_dir,
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
            "./channel/...",
        )

    if args.models:
        run_goose(goose_dir, "./model/channel")
        run_goose(goose_dir, "./model/strings")

    if args.std_lib:
        run_goose(
            goose_dir,
            "testing",
            "bytes",
            "context",
            "cmp",
            "unsafe",
            "crypto/ed25519",
            "crypto/rand",
            "errors",
            "io",
            "math",
            "math/big",
            "math/rand",
            "math/bits",
            "os",
            "runtime",
            "sort",
            "slices",
            "reflect",
            "strconv",
            "strings",
            "sync",
            "sync/atomic",
            "internal/synctest",
            "internal/race",
            "time",
            "fmt",
            "log",
            "encoding/binary",
        )

    for proj in projs:
        run_goose(
            proj_dir(proj.name),
            *proj.pkgs,
        )
    if args.lean:
        # Lean only: packages whose types (only) are translated, so that the
        # types of the packages above that refer to them can be translated
        if args.std_lib:
            run_goose(goose_dir, "internal/runtime/atomic", "internal/runtime/sys")
    pm.wait_all()


if __name__ == "__main__":
    main()
