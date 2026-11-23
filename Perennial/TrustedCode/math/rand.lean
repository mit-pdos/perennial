/-
Trusted code for the Go `math/rand` package, in namespace `math.rand` (as the generated
package).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.sync.atomic

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial
noncomputable section

namespace math.rand
section code
variable [GooseExts] [GoGlobalContext]

/-- `runtime_rand()` (`math/rand/rand.go`), which has no Go body:

```go
//go:linkname runtime_rand runtime.rand
func runtime_rand() uint64
```

It is the runtime's `rand` (`runtime/rand.go`: `func rand() uint64`, "a random uint64 from the
per-m chacha8 state"), which loops on the `m`'s ChaCha8 generator (`c.Next()`, refilling it with
`c.Refill()` when it runs out) and returns its next 64 bits; it takes no lock and cannot fail.
The model returns an arbitrary `uint64` (`ArbitraryInt`), and cannot panic either: every result
of the runtime's is one of the model's (the distribution is not modelled). -/
def runtime_rand.impl : val :=
  λ: <>, ArbitraryInt

/-- `math/rand.Rand`, named by its string (this file comes before the generated code). -/
def randTy : go.GoType := go.GoType.Named go!"math/rand.Rand" []

/-- `math/rand.runtimeSource`, named by its string. -/
def runtimeSourceTy : go.GoType := go.GoType.Named go!"math/rand.runtimeSource" []

/-- The type of `globalRandGenerator`, `atomic.Pointer[Rand]`. -/
def globalRandGeneratorTy : go.GoType := sync.atomic.Pointer.ty randTy

/-- `globalRand()` (`math/rand/rand.go`), the generator of the top-level functions:

```go
func globalRand() *Rand {
	if r := globalRandGenerator.Load(); r != nil {
		return r
	}

	// This is the first call. Initialize based on GODEBUG.
	var r *Rand
	if randautoseed.Value() == "0" {
		randautoseed.IncNonDefault()
		r = New(new(lockedSource))
		r.Seed(1)
	} else {
		r = &Rand{
			src: &runtimeSource{},
			s64: &runtimeSource{},
		}
	}

	if !globalRandGenerator.CompareAndSwap(nil, r) {
		// Two different goroutines called some top-level
		// function at the same time. [...]
		// Just use the first one to get in.
		return globalRandGenerator.Load()
	}

	return r
}
```

The model is Go's body with the test of `randautoseed` (a `GODEBUG` setting, read through
`internal/godebug`, which is not translated) replaced by its default outcome: the `else` branch,
the generator over the runtime's source, as goose would translate it (`r` is a local, not a
heap cell, and the `Rand`'s two `*runtimeSource`s are stored converted to the interface types of
the fields, `Source` and `Source64`, as the composite literal's element conversions do).

Why the other outcome needs no model. `randautoseed.Value()` is `"0"` only if the program runs
with `GODEBUG=randautoseed=0` (in the environment, or by a `//go:debug` directive or the
`godebug` line of the main module's `go.mod`). Go then makes the generator a `Rand` over a
`lockedSource` seeded with 1, whose `Int63` (`lockedSource.Int63`: a mutex around
`rngSource.Int63`, `int64(rng.Uint64() & rngMask)`) returns a value in `[0, 2^63)` and cannot
panic; so do its `Uint64` and its `Seed`. The only readers of the generator are the top-level
functions, through `globalRand`; the translated ones (`Int63`, `Int31`, `Int63n`, ...) only call
`Int63` and `Uint64` on it (through `Rand`'s methods), whose every sequence of results under the
`lockedSource` is a sequence of results of the model's `runtimeSource` (`runtime_rand` above is
arbitrary, and `runtimeSource.Int63` masks it to `[0, 2^63)`). The functions that would tell the
two sources apart (`Seed`, which re-seeds a `lockedSource` and switches a `runtimeSource` to one,
and `Read`, `Float64`, ... on the generator's state) are not translated: a call of one is stuck.
`Seed` is also the only writer of `globalRandGenerator` other than `globalRand`; with `Seed`
stuck, the model's `CompareAndSwap(nil, r)` races only with other `globalRand`s, as in Go. (An
unverified `Seed` with `GODEBUG=randseednop=0` in the same program would make the generator a
`lockedSource`, whose methods are not translated: the model is then stuck where Go runs, less
defined, never more.) -/
def globalRand.impl : val :=
  λ: <>,
    let: "g" := GlobalVarAddr go!"math/rand.globalRandGenerator" #() in
    let: "cur" := (MethodResolve (go.PointerType globalRandGeneratorTy) go!"Load") "g" #() in
    if: "cur" ≠⟨go.PointerType randTy⟩ #null then "cur"
    else
      let: "r" := GoAlloc randTy (CompositeLiteral randTy (LiteralValue [
        KeyedElement (some (KeyField go!"src")) (ElementExpression (go.PointerType runtimeSourceTy)
          (GoAlloc runtimeSourceTy (CompositeLiteral runtimeSourceTy (LiteralValue [])))),
        KeyedElement (some (KeyField go!"s64")) (ElementExpression (go.PointerType runtimeSourceTy)
          (GoAlloc runtimeSourceTy (CompositeLiteral runtimeSourceTy (LiteralValue []))))
      ])) in
      if: (MethodResolve (go.PointerType globalRandGeneratorTy) go!"CompareAndSwap") "g" #null "r"
      then "r"
      else (MethodResolve (go.PointerType globalRandGeneratorTy) go!"Load") "g" #()

end code
end math.rand

end

end Perennial
