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

/-- **The run's `fips140` GODEBUG setting**: the string `godebug.New("fips140").Value()` returns
when `crypto/fips140` is initialized. Go's runtime hands `internal/godebug` the process's
`GODEBUG` environment variable and the binary's default GODEBUG (set by the go command from
`go.mod`'s `go` and `godebug` lines and the main package's `//go:debug` directives); the
`fips140` entry of the variable takes precedence over the default (`godebug.update`), and the
setting is immutable (`internal/godebugs`: `Immutable: true`), so a later
`os.Setenv("GODEBUG", ...)` does not change it.

The model has no process environment, so the value is opaque: nothing is known or proved about
it, and a theorem about a program holds for every value it could be. A theorem that needs a
particular value takes it as a premise (`GodebugFips140Off`). -/
opaque godebugFips140 : GoString

/-- **Environment premise: the `fips140` GODEBUG setting is unset or `off`** (`godebugFips140`
is `""` or `"off"`): `GODEBUG` has no `fips140=` entry, or its last one is `fips140=off`, and
the binary's default sets no other value (in particular, no `fips140=only`, in which mode
`crypto/sha1.Sum` panics).

A top-level theorem about a program whose proof needs it names it as a hypothesis, and then
covers only the runs with that setting. It is not of the overflow kind of `README.md`'s model
assumptions: `GODEBUG=fips140=only` is a setting a real run can have. It is the condition under
which the packages around `crypto/fips140` that goose does not translate do not panic: with
any other value, `crypto/internal/fips140`'s initializer panics (an unknown value) or sets
`fips140.Enabled`, and then `crypto/internal/fips140/check`'s initializer panics, as the
standard library is translated with the `purego` build tag (`fips140.Supported`: "FIPS 140-3
mode is incompatible with the purego build tag"). -/
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
`internal/godebugs.Lookup`, which lists `fips140`, so its "not listed" panic is unreachable),
and returns the text the runtime last stored for it through the update function that
`internal/godebug`'s `init` registers with the runtime's `go:linkname`ed `setUpdate`, or `""`
when a `#`-pattern of `internal/bisect` does not match the caller's stack; it cannot panic for
this name. That text is `godebugFips140`.

The model allocates the variable and stores `godebugFips140 == "only"`, which is Go's value. It
cannot panic, nor can Go's initializer. The allocation and lookup in `internal/godebug`'s own
state are not modelled: no translated code reads that state. -/
def enabled.init : val :=
  λ: <>,
    go.GlobalAlloc go!"crypto/fips140.enabled" go.bool #() ;;
    GlobalVarAddr go!"crypto/fips140.enabled" #() <-[go.bool]
      #(decide (godebugFips140 = go!"only"))

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
