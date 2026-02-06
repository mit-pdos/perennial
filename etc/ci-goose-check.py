#!/usr/bin/env python3

from dataclasses import dataclass
import subprocess as sp
import shutil
import argparse
import re
from typing import Optional


@dataclass
class Proj:
    name: str
    repo: str
    # default branch if None
    commit: Optional[str]
    # separate branch for old goose
    commit_old: Optional[str]

    def path(self) -> str:
        return f"/tmp/{self.name}"

    @classmethod
    def make(cls, name, repo, commit=None, old=None):
        return cls(name, repo, commit, old or commit)


projs = {
    "goose": Proj.make("goose", "https://github.com/goose-lang/goose/", commit="upamanyus-fixes"),
    "std": Proj.make("std", "https://github.com/goose-lang/std", commit="upamanyus-fixes"),
    "primitive": Proj.make("primitive", "https://github.com/goose-lang/primitive", commit="upamanyus-fixes"),
    "marshal": Proj.make("marshal", "https://github.com/tchajed/marshal"),
    "examples": Proj.make("examples", "https://github.com/mit-pdos/perennial-examples"),
    "gokv": Proj.make("gokv", "https://github.com/mit-pdos/gokv", commit="upamanyus-fixes"),
    "etcd-raft": Proj.make("etcd-raft", "https://github.com/upamanyus/etcd-raft"),
    "etcd": Proj.make("etcd", "https://github.com/upamanyus/etcd"),
}


def checkout(proj: Proj):
    print(f"Checking out {proj.name}")
    path = proj.path()
    shared_args = {"check": True, "cwd": path}

    try:
        p = sp.run(
            ["git", "remote", "get-url", "origin"],
            text=True,
            capture_output=True,
            **shared_args,
        )
        assert p.stdout.strip() == proj.repo
        sp.run(["git", "reset", "--hard"], **shared_args)
        sp.run(["git", "pull"], **shared_args)
    except (FileNotFoundError, sp.CalledProcessError, AssertionError):
        shutil.rmtree(path, ignore_errors=True)
        sp.run(["git", "clone", proj.repo, path], check=True)

    if proj.commit is not None:
        sp.run(["git", "checkout", proj.commit], **shared_args)


def parse_github_tree_url(url):
    m = re.match(r"(?P<repo>https://github.com/.*)/tree/(?P<commit>.*)", url)
    if m is None:
        raise ValueError(f"Invalid GitHub tree URL: {url}")
    return m["repo"], m["commit"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--goose-url",
        default="https://github.com/goose-lang/goose/tree/new",
        help="location of goose",
    )

    args = parser.parse_args()
    if args.goose_url == "":
        args.goose_url = "https://github.com/goose-lang/goose/tree/new"
    goose_repo, goose_commit = parse_github_tree_url(args.goose_url)

    projs["goose"].repo = goose_repo
    projs["goose"].commit = goose_commit

    for proj in projs.values():
        checkout(proj)

    print("\nRunning Goose")
    sp.run(
        [
            "new/etc/update-goose-new.py",
            "--compile",
            "--goose",
            projs["goose"].path(),
            "--std-lib",
            "--goose-examples",
            "--models",
            "--gokv",
            projs["gokv"].path(),
            "--marshal",
            projs["marshal"].path(),
            "--std",
            projs["std"].path(),
            "--primitive",
            projs["primitive"].path(),
            "--etcd",
            projs["etcd"].path(),
            "--etcd-raft",
            projs["etcd-raft"].path(),
        ],
        check=True,
    )

    print("\nSeeing if anything is out of sync")
    sp.run(["git", "diff", "--exit-code"], check=True)
    print("\nSuccess!")


if __name__ == "__main__":
    main()
