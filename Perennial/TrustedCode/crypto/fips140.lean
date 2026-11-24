/-
Trusted code for the Go `crypto/fips140` package, in namespace `crypto.fips140` (as the
generated package): what `Enforced` (translated) reads that has no Go body in the package, the
variable `enabled` (a read of the `fips140` GODEBUG setting) and `isBypassed` (a `go:linkname`
into the runtime), and the environment premise `GodebugFips140Off` about that setting.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace crypto.fips140

/-- **The run's `fips140` GODEBUG setting**: its text, without the `#`-pattern of
`internal/bisect` a setting may carry (`fips140=only#pattern`). Go's runtime hands
`internal/godebug` the process's `GODEBUG` environment variable and the binary's default GODEBUG
(set by the go command from `go.mod`'s `go` and `godebug` lines and the main package's
`//go:debug` directives); the last `fips140=` entry of the variable takes precedence over the
default (`godebug.update`). The setting is immutable (`internal/godebugs`: `Immutable: true`):
it is fixed when `internal/godebug` first records it, at the latest by the first read
(`crypto/internal/fips140`'s initializer, which runs before `crypto/fips140`'s), so an
`os.Setenv("GODEBUG", ...)` that runs earlier can still set it, and none that runs later can.

The model has no process environment, so the value is opaque: nothing is known or proved about
it, and a theorem about a program holds for every value it could be. A theorem that needs a
particular value takes it as a premise (`GodebugFips140Off`). -/
opaque godebugFips140 : GoString

/-- **Environment premise: the `fips140` GODEBUG setting is unset or `off`** (`godebugFips140`
is `""` or `"off"`): the setting in effect (see `godebugFips140`) is not `on`, `only`, `debug`
or another value, whatever `#`-pattern follows it; in particular, not `fips140=only`, in which
mode `crypto/sha1.Sum` panics.

A top-level theorem about a program whose proof needs it names it as a hypothesis, and then
covers only the runs with that setting. It is not of the overflow kind of `README.md`'s model
assumptions: `GODEBUG=fips140=only` is a setting a real run can have. It is also the condition
under which the packages around `crypto/fips140` that goose does not translate (their
initializers are not run by the model) do not panic: every read of the setting then returns
`""` or `"off"`, so `crypto/internal/fips140`'s initializer neither panics on an unknown value
nor sets `fips140.Enabled`, and `crypto/internal/fips140/check`'s initializer returns at once.
With `on`, `only` or `debug` read there, it panics, as the standard library is translated with
the `purego` build tag (`fips140.Supported`: "FIPS 140-3 mode is incompatible with the purego
build tag"); a `#`-pattern can make that read return the text while `crypto/fips140`'s returns
`""`, which is why the premise is on the text, not on what `crypto/fips140` reads. -/
def GodebugFips140Off : Prop :=
  godebugFips140 = go!"" ∨ godebugFips140 = go!"off"

section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `enabled` (`enforcement.go`):

```go
var enabled = godebug.New("fips140").Value() == "only"
```

`internal/godebug` is not translated. `New(name)` is `return &Setting{name: name}`, an
allocation. `Value()` looks the setting up once (`sync.Once`, a `sync.Map` of settings,
`internal/godebugs.Lookup`, which lists `fips140`, so its "not listed" panic is unreachable)
and returns the setting's text, `godebugFips140`; when the setting carries a `#`-pattern, it
returns `""` instead if the pattern does not match the caller's stack
(`bisect.Matcher.Stack`, which may also print a match line to standard error). It cannot panic
for this name.

The model allocates the variable and stores `godebugFips140 == "only"` or `false`, chosen
arbitrarily (`false` covers a pattern that does not match), so every value Go can store is one
of its results. It cannot panic, nor can Go's initializer. Not modelled: `internal/godebug`'s
own state (no translated code reads it) and a bisect match line on standard error. -/
def enabled.init : val :=
  λ: <>,
    go.GlobalAlloc go!"crypto/fips140.enabled" go.bool #() ;;
    GlobalVarAddr go!"crypto/fips140.enabled" #() <-[go.bool]
      (if: ArbitraryInt =⟨go.int64⟩ #(W64 0)
       then #(decide (godebugFips140 = go!"only"))
       else #false)

/-- `isBypassed() bool` (`enforcement.go`: `//go:linkname isBypassed`, no Go body): the
runtime's `fips140_isBypassed` (`runtime/fipsbypass.go`), `return getg().fipsOnlyBypass`, the
calling goroutine's flag, which `WithoutEnforcement` sets for the duration of its callback
(`setBypass`, `unsetBypass`, also `go:linkname`s, not modelled) and a new goroutine inherits.
The model: an arbitrary `bool`, which covers both values. It cannot panic, nor can Go's. -/
def isBypassed.impl : val :=
  λ: <>,
    ArbitraryInt =⟨go.int64⟩ #(W64 0)

end code
end crypto.fips140

end Perennial
