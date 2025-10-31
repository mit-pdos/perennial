# Contributing to Perennial

## Default build

Not everything in the repo is built by default, even in CI. In order to be
compiled, a file must be `Require`d from `src/ShouldBuild.vo` (which already includes
`new/should_build.vo` for new goose proofs).

## CI notes

Rocq's CI checks the Perennial build on every commit to Rocq. In order to avoid
breaking Rocq CI, they build a branch called `coq/tested` which we push to
automatically only when perennial master's CI passes. They also only run `make
lite`, which compiles `src/LiteBuild.v`, a representative subset of Perennial
that takes much less time to build.

We skip running Qed commands in CI using
[etc/disable-qed.sh](./etc/disable-qed.sh) - see that script for details. This
reduces build times by about 10%.

## Maintaining dependencies

There are a few dependencies managed as submodules in `external/`. To update
them, run `git submodule update --init --remote`, then commit the resulting
change with git.

The dependencies are frozen at a particular version to avoid breaking the
Perennial build when there are incompatible upstream changes. We use Dependabot
to do daily checks for dependency updates (see
[.github/dependabot.yml](.github/dependabot.yml) and read the GitHub
documentation). In addition, a workflow
[dependabot-automerge.yml](.github/workflows/dependabot-automerge.yml)
automatically merges these (this depends on a GitHub Ruleset to ensure CI passes
before the PR is merged).

## Tips for managing compilation time

Perennial takes about 180 CPU minutes to compile. Compiling in parallel with
`make -j4` (or more) is significantly faster, and can cut the time down to 40-50
minutes. Incremental builds are generally much faster.

You can compile individual files by simply running `make` with the path to a
specific `.vo` output file. We often run `make new/should_build.vo` to build a
file which depends on everything in new goose that is currently maintained, for exammple.

When you make a change to a dependency, you can keep working without fully
compiling the dependency by compiling `vos` interface files, which skips proofs.
The simplest way to do this is just to run `make vos`, but you can do a more
targeted build, like `make src/program_proof/wal/proof.required_vos`, which only
builds the vos dependencies to work on the `wal/proof.v` file.

Rocq also has a feature called `vok` compilation, where Rocq compiles a file
using only `vos` files for its dependencies. The process does not produce a
self-contained `vo` file, but emits an empty `vok` file to record that checking
is complete. Similar to compiling a single `vo` file, you can build a single
`vok` file, which will be much faster at compiling the dependencies. Using `vos` and `vok` files can significantly speed up the
edit-compile-debug cycle. Note that `vok` checking isn't the same as regular
compilation - it doesn't check universe constraints.

We compile with [rocqc.py](etc/rocqc.py), a Python wrapper around `rocq compile`
to get timing information. You can compile without timing information with `make
TIMED=false`. To read the results of the timing, run `uv run ./etc/timing-report.py`;
use `--help` to access some other features.

## Updating Goose output

This repo has committed versions of the output of Goose, to avoid making Goose
and all the projects involved dependencies for compilation. You should update
these using the `./etc/update-goose.py` and `./new/etc/update-goose.py` scripts,
which record exactly how to generate the output for the various Goose projects
we have (in particular, the list of packages that should be translated).

You can run `./etc/ci-goose-check.py` to clone all the projects whose proofs are
included in this repo and run both update-goose scripts. This is what the
check-goose CI job does.

You can use `./etc/update-goose.py -a` to build all supported projects, assuming
they are checked out as siblings.

If you submit a PR to goose that changes the output, submit a PR to perennial
(this repo) in parallel and **link to the goose PR in the description**. This link
causes the perennial CI to build against your PR, so that the CI check-goose job
passes while the goose PR is open. This feature is implemented by
`etc/ci-use-goose-pr`, which reads the PR description and identifies the
corresponding goose branch using the GitHub API.

## Integer templating

Some files have templates that are used to support the various integer types by
copy-pasting:

```bash
./etc/int_template.py new/proof/sync/atomic.v
./etc/int_template.py new/trusted_code/sync/atomic.v
```

## Formatting / Linting

- `python`: we run [ruff](https://github.com/astral-sh/ruff) in CI
  to lint and format all our Python code.
  Run it locally with `ruff format` and `ruff check`.
- `toml`: we run [taplo](https://taplo.tamasfe.dev/) in CI
  to format all our toml files.
  Run it locally with `taplo format`.
