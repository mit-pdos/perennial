# opam guide for perennial

You should already have opam installed, because you have rocq installed via opam.

If you haven't already, add the rocq opam repo to your switch: `opam repo add rocq-released https://rocq-prover.org/opam/released`

To install perennial's dependencies and **on any upstream changes** you need to run these:

```
opam pin add -n .
opam install --deps-only -y ./perennial.opam
```

As far as I can tell the latter ought to do the pinning but does not.

Some random facts:

- An opam switch is a directory in `~/.opam` that has some opam repos, metadata for installed packages, pinning info, and clean build copies. You can use multiple opam switches to isolate different sets of dependencies. Note that switches share essentially nothing, so you'll have two copies of rocq, stdpp, iris, etc.
- Whenever a package is installed, it is built in its own build directory - for example a git project is locally cloned and then compiled. This means that builds are isolated from your source directory.
- An opam "package" is just a name. opam generally relies on the (assumed global) opam _repositories_ to figure out what a package is (e.g., where the source code is and what the build/install steps are). When you use pin-depends you somewhat break this: pinning that dependency makes it available without a repo. opam doesn't like this but we use it to avoid publishing perennial to some repo, the way iris does.

## Updating dependencies

Run `perennial-cli opam update`. To install perennial-cli, you can use `go install github.com/mit-pdos/perennial-cli@latest`. Alternately, you can run without installing with `go run`.

## Testing reverse dependencies

Suppose you have a local change to perennial and want to test the repos that depend on perennial ("reverse dependencies").

Compile perennial as normal.

Then you can install from your build directory:

```
make new-goose
opam install ./perennial.opam --assume-built
```

(You should make sure everything in `make new-goose` is compiled, in case something isn't part of src/ShouldBuild.v)

Now just go to each repo and run `dune build`.

## Useful opam commands

`opam list --pinned --wrap`
`opam install --working-dir`
