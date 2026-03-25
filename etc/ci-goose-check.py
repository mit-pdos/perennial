#!/usr/bin/env python3

from dataclasses import dataclass
import subprocess as sp
import shutil
from typing import Optional


@dataclass
class Proj:
    name: str
    repo: str
    commit: Optional[str]

    def path(self) -> str:
        return f"/tmp/{self.name}"

    @classmethod
    def make(cls, name, repo, commit=None):
        return cls(name, repo, commit)


projs = {
    "std": Proj.make(
        "std", "https://github.com/goose-lang/std", commit="upamanyus-fixes"
    ),
    "primitive": Proj.make(
        "primitive", "https://github.com/goose-lang/primitive", commit="upamanyus-fixes"
    ),
    "marshal": Proj.make(
        "marshal", "https://github.com/upamanyus/marshal", commit="upamanyus-fixes"
    ),
    "examples": Proj.make("examples", "https://github.com/mit-pdos/perennial-examples"),
    "etcd-raft": Proj.make(
        "etcd-raft", "https://github.com/upamanyus/etcd-raft", commit="goose"
    ),
    "etcd": Proj.make(
        "etcd",
        "https://github.com/upamanyus/etcd",
        commit="4c11e0db9815f8e1d584cafd79b3feff8e4d06fb",
    ),
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


def main():
    for proj in projs.values():
        checkout(proj)

    print("\nRunning Goose")
    sp.run(
        [
            "new/etc/update-goose-new.py",
            "--compile",
            "--std-lib",
            "--goose-examples",
            "--models",
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
