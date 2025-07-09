#!/usr/bin/env python3

from dataclasses import dataclass
import subprocess as sp
import shutil
import argparse
import re


@dataclass
class Proj:
    name: str
    repo: str
    commit: str

    def path(self) -> str:
        return f"/tmp/{self.name}"


projs = {
    "goose": Proj("goose", "https://github.com/goose-lang/goose/", "master"),
    "new_goose": Proj("new_goose", "https://github.com/goose-lang/goose/", "new"),
    "std": Proj("std", "https://github.com/goose-lang/std", "master"),
    "primitive": Proj("primitive", "https://github.com/goose-lang/primitive", "main"),
    "marshal": Proj("marshal", "https://github.com/tchajed/marshal", "master"),
    "examples": Proj(
        "examples", "https://github.com/mit-pdos/perennial-examples", "master"
    ),
    "journal": Proj("journal", "https://github.com/mit-pdos/go-journal", "master"),
    "nfsd": Proj("nfsd", "https://github.com/mit-pdos/go-nfsd", "master"),
    "gokv": Proj("gokv", "https://github.com/mit-pdos/gokv", "main"),
    "new_gokv": Proj("new_gokv", "https://github.com/mit-pdos/gokv", "new"),
    "mvcc": Proj("mvcc", "https://github.com/mit-pdos/vmvcc", "main"),
    "pav": Proj("pav", "https://github.com/sanjit-bhat/pav", "main"),
    "etcd-raft": Proj("etcd-raft", "https://github.com/upamanyus/etcd-raft", "main"),
    "etcd": Proj("etcd", "https://github.com/upamanyus/etcd", "main"),
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

    sp.run(["git", "checkout", proj.commit], **shared_args)


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
        checkout(proj)

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
            "--journal",
            projs["journal"].path(),
            "--nfsd",
            projs["nfsd"].path(),
            "--gokv",
            projs["gokv"].path(),
            "--mvcc",
            projs["mvcc"].path(),
        ],
        check=True,
    )

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
            "--go-journal",
            projs["journal"].path(),
            "--pav",
            projs["pav"].path(),
        ],
        check=True,
    )

    print("\nSeeing if anything is out of sync")
    sp.run(["git", "diff", "--exit-code"], check=True)
    print("\nSuccess!")


if __name__ == "__main__":
    main()
