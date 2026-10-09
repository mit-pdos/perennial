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
def Log.ty [FfiSyntax] [GoGlobalContext] : go.GoType :=
  (go.GoType.Named go!"github.com/mit-pdos/perennial/goose/testdata/examples/append_log.Log" [])

structure Log [FfiSyntax] where
  mk ::
  m' : Loc
  sz' : w64
  diskSz' : w64
```

and each function to a GooseLang `val` (`noncomputable def Open.impl ... : val`),
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
