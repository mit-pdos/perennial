#!/usr/bin/env python3

import shutil
import subprocess as sp
from dataclasses import dataclass


@dataclass
class Proj:
    name: str
    repo: str
    commit: str

    def path(self) -> str:
        return f"/tmp/{self.name}"


projs = {
    "gokv": Proj("gokv", "https://github.com/mit-pdos/gokv", "main"),
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


for proj in projs.values():
    checkout(proj)

print("\nRunning Grackle")
sp.run(
    [
        "etc/update-grackle.sh",
        "--gokv",
        projs["gokv"].path(),
    ],
    check=True,
)
