#!/usr/bin/env python3

import argparse
import subprocess
import sys


def run_sed(script, files):
    cmd = ["sed", "-E", "-i", ""] + script + files
    subprocess.run(cmd, check=True)


def main():
    """
    notes:
    - full line match "^line$" for idempotence.
    - intentionally doesn't work for one-liners "Proof. blah. Qed.",
        as that would complicate idempotence.
    - capture group "([[:space:]]*)" & "\1" to preserve whitespace for indented proofs.
    """
    p = argparse.ArgumentParser(
        description="Toggle Rocq proofs between 'admit' and 'prove' modes using sed (idempotent)."
    )
    p.add_argument("mode", choices=["admit", "prove"])
    p.add_argument("file", nargs="+")
    args = p.parse_args()

    if args.mode == "admit":
        script = [
            r"-e",
            r"s/^([[:space:]]*)Proof\.$/\1Admitted. (* Proof./",
            r"-e",
            r"s/^([[:space:]]*)Qed\.$/\1Qed. *)/",
            r"-e",
            r"s/^([[:space:]]*)Admitted\.$/\1Admitted. *)/",
        ]
    else:  # prove mode (reverse)
        script = [
            r"-e",
            r"s/^([[:space:]]*)Admitted\.[[:space:]]\(\*[[:space:]]Proof\.$/\1Proof./",
            r"-e",
            r"s/^([[:space:]]*)Qed\.[[:space:]]\*\)$/\1Qed./",
            r"-e",
            r"s/^([[:space:]]*)Admitted\.[[:space:]]\*\)$/\1Admitted./",
        ]

    try:
        run_sed(script, args.file)
    except subprocess.CalledProcessError as e:
        print(f"sed failed: {e}", file=sys.stderr)
        sys.exit(e.returncode)

    print(f"OK: applied '{args.mode}' to {args.file}")


if __name__ == "__main__":
    main()
