# Goose: translating Go to GooseLang

Goose translates a subset of Go into GooseLang, the language Perennial gives a
semantics to, emitting Lean 4 modules that are checked as part of Perennial
(`Perennial/Code/**`). Its companion `proofgen` emits the generated proofs for
the translated types (`Perennial/GeneratedProof/**`). The translator is
trusted: the process can be viewed as giving a semantics to Go.

Goose supports a reasonable subset of Go, enough to write serious concurrent
programs. GooseLang is an untyped lambda calculus with references and
concurrency, with special support for Go's types, slices, maps, channels,
interfaces and `defer`.

## Example

For `testdata/examples/append_log`, the Go type

```go
type Log struct {
	m      *sync.Mutex
	sz     uint64
	diskSz uint64
}
```

is translated (in `append_log.gold.lean`) to a type descriptor, a Lean
structure for its values and its underlying struct type:

```lean
def Log.ty [GooseExts] [GoGlobalContext] : go.GoType :=
  (go.GoType.Named go!"github.com/mit-pdos/perennial/goose/testdata/examples/append_log.Log" [])

structure Log [GooseExts] where
  mk ::
  m' : Loc
  sz' : w64
  diskSz' : w64
```

An unnamed struct type with fields is translated the same way, without the
`go.Named` descriptor: a structure `«struct#<h>»` (`<h>` a hash of the type,
`util.AnonStructName`), its field list, `«struct#<h>».underlying` (the type the
translation writes for it) and its `TypeAssumptions` class, once per package
(`anon_structs.go`).

Each function is translated to a GooseLang `val` (`noncomputable def Open.impl ... : val`),
printed as plain constructor applications of `Perennial/GooseLang/Lang.lean`.

## Running goose

The usual way to run goose is `etc/update-goose-new.py` (see its `--help`),
which regenerates the translations checked into Perennial. It runs, for each
package,

```
goose -out Perennial/Code -configdir Perennial/Code -dir <module> <packages>
proofgen -out Perennial/GeneratedProof -configdir Perennial/Code -dir <module> <packages>
```

A package's translation is configured by `<path>.toml` in the config directory
(see `declfilter/declfilter.go`): which declarations to translate, axiomatize
or trust, and bootstrapping options. `-lean-root PKG=ROOT` places the modules
of the packages under Go path `PKG` under the Lean module root `ROOT` instead
of `Perennial`, for projects that translate their own Go packages.
`-tags TAG,...` (as `go build -tags`) loads the packages with those Go build
tags in addition to `goose`, which is always set: it selects the files under
build constraints (`//go:build with_tla`). `goose`, `proofgen`, `modelcheck`
and `skiplint` take it, and must be given the same tags for a package. Build tags are those
of a whole Go build: translate every package of a program with the same tags
(a package translated with a tag and a dependency translated without it are
not the code of any one build), and state results about the program built
with `-tags goose,TAG,...`. The translation does not record the tags.
`-overlay FILE` takes a JSON file in the format of `go build -overlay`,
`{"Replace": {"<path>": "<replacement>", ...}}`: the packages are loaded as if
each path had the contents of its replacement, so a file added to a package
(a path that does not exist) or replaced in it is type-checked and translated
as part of that package, under the same build constraints as the package's own
files (an overlay file `//go:build goose || TAG` is translated, one
`//go:build !goose` is not). This translates code generated for verification
(say, extra methods of a package's types) along with a package pinned at a
fixed revision, without changing its source. Relative paths are relative to
the current directory, as for the go command; deleting a file (an empty
replacement) is not supported. `goose`, `proofgen`, `modelcheck` and
`skiplint` take it, and must be given the same overlay for a package, as for
`-tags`; what is verified is then the program built with that overlay (`go
build -overlay FILE -tags goose,...`). The translation does not record the
overlay, but the `go:` positions of an overlay file's declarations name the
file at its overlay path.

**Go model overlays.** A package's config may have a `[model]` table
(`declfilter.ModelConfig`): `dir`, a directory of Go model files in the
package's own package clause, relative to the repository root (the nearest
ancestor of `-configdir` with a lakefile, or `-model-root DIR`), and
`replaces`, the real declarations they replace (`f`, `T.m`, `T`, `X`, or
`init.N`, whose model `init` is marked `//gomodel:replace init.N "<first line
of the real body>"`; `["*"]` replaces every real file, and may add a
standard-library package; `[]` only adds). `added_methods` lists the methods
the model may add to the real types. The builder (`util.BuildModels`, used by
`goose`, `proofgen`, `modelcheck` and `skiplint` through `util.LoadPackages`)
covers every package of the import graph with a `[model]` table: it deletes
each replaced declaration (with its doc comment and `//go:linkname`) and puts
the model's in its place between `//line` directives, so the real file order,
`init` order and variable-initialization order are kept and the `go:`
positions name the model file; an import the model needs is added, one only
the deleted code used becomes `_`; the model's other declarations (additions)
go in `zz_gomodel_<file>.go` (their `init`s run after the real ones; their
variables initialize in dependency order, after the real ones they do not
feed). It refuses a model whose `replaces` does not
match both ways, that shadows a real declaration, or that changes the real
package's API (a replaced function's, method's or variable's type; a replaced
type's exported fields, kind or comparability; a real type's method set
beyond `added_methods`). The model's declarations are translated, except
those the config trusts (primitive stubs, with a `.impl` in TrustedCode).
`goose model-overlay -o DIR <packages>` writes the same overlay for `go
build/test -overlay DIR/overlay.json`; what is verified is the program built
with it, under the same build configuration (linux/amd64, `-tags goose,...`:
the files of a package, and so the splice, depend on it). A model file has no
build constraint, no GOOS/GOARCH suffix and no `//line` directive, and
declares no predeclared identifier. Model files live in a module nothing builds
(`goose/model/overlay/<import path>`); the standard-library models' choice and
stuck points are `internal/gomodel`'s `Choose`, `ChooseUint64` and `Stuck`, a
package the overlay adds (go1.26.0's `go list` does not find such a package
through `go/packages`; go1.26.11 and go1.27 do). The gold example is
`testdata/examples/modeloverlay`.

The output for a large package is split into modules `<pkg>/chunkN` that lake
checks in parallel, re-exported by the package's module, which downstream code
imports as usual: goose puts the `TypeAssumptions` classes in chunks of their
own (`leanChunks` in `interface.go`), and proofgen splits the generated proofs
by type (`leanChunks` in `proofgen/proofgen.go`).

## Developing goose

The translation from Go is in `goose.go` (expressions and statements),
`types.go` and `lean_types.go` (types), and `interface.go` (packages). The
GooseLang syntax is in `glang/syntax.go`, and `glang/lean.go` prints it as Lean.

Goose has integration tests that translate example code and compare against a
"gold" file in the repo (`testdata/examples/**/<pkg>.gold.lean`). Changes to
these gold files are hand-audited when they are initially created, and then the
test ensures that previously-working code continues to translate correctly. To
update the gold files after modifying the tests or fixing goose, run
`go test -update-gold` (and manually review the diff before committing). Some
of the examples are also translated into Perennial (`--goose-examples` of
`etc/update-goose-new.py`), which checks that the output elaborates.

The tests include `testdata/examples/unittest`, a collection of small examples
intended for wide coverage, as well as some real programs in other directories
within `testdata/examples`. `testdata/negative-tests` has code that goose must
reject.

The `testdata/examples/semantics` package contains semantic tests, functions of
the form `func test*() bool` that return true (helper functions should _not_
follow this pattern). `cmd/test_gen` generates `generated_test.go`, a Go test
suite checking that they do return true; regenerate it with `go generate ./...`.

### Running tests

```
make ci
```

runs gofmt, `go vet` and all the tests. `make fix` fixes the formatting and
updates generated files.
