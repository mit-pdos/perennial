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
    "goose": Proj.make(
        "goose", "https://github.com/goose-lang/goose/", commit="master"
    ),
    "new_goose": Proj.make(
        "new_goose", "https://github.com/goose-lang/goose/", commit="new"
    ),
    # starting in v0.7.0, std uses features only supported by new goose
    "std": Proj.make(
        "std", "https://github.com/goose-lang/std", commit="master", old="v0.6.1"
    ),
    "primitive": Proj.make("primitive", "https://github.com/goose-lang/primitive"),
    "marshal": Proj.make("marshal", "https://github.com/tchajed/marshal"),
    "examples": Proj.make("examples", "https://github.com/mit-pdos/perennial-examples"),
    "new_gokv": Proj.make("new_gokv", "https://github.com/mit-pdos/gokv", commit="new"),
    "etcd-raft": Proj.make("etcd-raft", "https://github.com/upamanyus/etcd-raft"),
    "etcd": Proj.make("etcd", "https://github.com/upamanyus/etcd"),
}


def checkout(proj: Proj, old: bool):
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

    commit = proj.commit
    if old:
        commit = proj.commit_old
    if commit is not None:
        sp.run(["git", "checkout", commit], **shared_args)


def parse_github_tree_url(url):
    m = re.match(r"(?P<repo>https://github.com/.*)/tree/(?P<commit>.*)", url)
    if m is None:
        raise ValueError(f"Invalid GitHub tree URL: {url}")
    return m["repo"], m["commit"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--new-goose-url",
        default="https://github.com/goose-lang/goose/tree/new",
        help="location of new goose",
    )

    args = parser.parse_args()
    if args.new_goose_url == "":
        args.new_goose_url = "https://github.com/goose-lang/goose/tree/new"
    new_goose_repo, new_goose_commit = parse_github_tree_url(args.new_goose_url)

    projs["new_goose"].repo = new_goose_repo
    projs["new_goose"].commit = new_goose_commit

    for proj in projs.values():
        checkout(proj, True)

    print("\nRunning Goose")
    sp.run(
        [
            "etc/update-goose.py",
            "--compile",
            "--goose",
            projs["goose"].path(),
            "--goose-examples",
            "--channel",
            "--std",
            projs["std"].path(),
            "--marshal",
            projs["marshal"].path(),
            "--examples",
            projs["examples"].path(),
        ],
        check=True,
    )

    for proj in projs.values():
        if proj.commit != proj.commit_old:
            checkout(proj, False)

    print("\nRunning new Goose")
    sp.run(
        [
            "new/etc/update-goose-new.py",
            "--compile",
            "--goose",
            projs["new_goose"].path(),
            "--std-lib",
            "--goose-examples",
            "--channel",
            "--gokv",
            projs["new_gokv"].path(),
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
