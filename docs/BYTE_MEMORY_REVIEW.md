# Byte memory: trusted-base review findings

A running record of the `/review-trusted` rounds on the byte-memory branch
(`worktree-byte-heap`): every problem found, the example that shows it, and
what was done. A BLOCK is a way for a Go program that panics (or computes
something else) to be verified; a REWORK adds trust that should not be there;
a NOTE records accepted trust or incompleteness. "Old semantics" is
`go.Semantics` (`Golang/Defn/Interface.lean`, `GoInterface` values); "byte
semantics" is `go.SemanticsB` (`Golang/Defn/StaticImage.lean`).

Most findings after round 4 are about goose rather than the new semantics:
both interface semantics compare dynamic types by their goose type terms
(`typeAddr t`, `ii.ty = t`), so every way goose gives one term to two Go types
makes a panicking type assertion verifiable.

## Round 1

**BLOCK: `False` from `go.SemanticsB` (two untyped-nil conversions).**
`PredeclaredSemantics` converted untyped `nil` to an interface type with the
old nil interface, and `InterfaceSemanticsB` with `(0, 0)`: two deterministic
steps for one instruction. *Fixed*: the old rule moved to `go.Semantics`
(`convert_nil_interface`).

## Round 2

**BLOCK: `False` from `go.BytesSemantics` (a proof chooses the layout).** The
encoding steps quantified over any `ByteRepr V` instance; a second lawful
layout of `Bool` gave two sizes for `SizeOf go.bool`. *Fixed*: the layout is
a function of the type (`layoutOf`, `TypeBytes t V`).

**BLOCK: interface conversion kept the source itab.** Between two named
interfaces with the same underlying type, core `convert_underlying` made the
conversion the identity, while Go gives the value an itab for the target.
*Fixed*: `convert_underlying` takes `NotInterface` of the target; the byte
conversion is the identity only from the same type.

## Round 3

**REWORK: fake `Panic`s.** "not modelled" cases (getitab, `==` on equal
dynamic types) were `Panic "... not modelled"`, which reads as Go behaviour.
*Fixed*: no rule (`NoGetitab`; `==` only for different or nil type words).

**REWORK: `DecodeBytes` panicked on bytes that are not an encoding** (Go has
no such panic). *Fixed*: it steps only on `encode x`.

**BLOCK: an `I1` value read as an `I2` passed `.(T)`.**

```go
type I1 interface{ M() }
type I2 interface{ M() }
type T struct{ x int }
func (T) M() {}

func main() {
	var a I1 = T{1}
	b := *(*I2)(&a)   // or *(*I2)(unsafe.Pointer(&a))
	_ = b.(T)         // Go: panic: interface conversion: main.I2 is main.T, not main.T (types from different scopes)
}
```

The model compared only `itab.Type`; Go compares the itab with
`go:itab.T,I2`. Round 3 removed the `(*I2)(&a)` route
(`convert_pointer_same_underlying` with `NotInterface`); the
`unsafe.Pointer` route stayed open. *Fixed in round 4.*

## Round 4

**BLOCK (round 3's, continued).** *Fixed*: `TypeAssert from_ t` carries the
source type (goose emits it; generated code regenerated); from a non-empty
`I` the assertion checks `itab.Type = typeAddr T` and `itab.Inter = typeAddr
I`; every lowering dispatches on the static source type, never on the
value's tag. The round-3 restriction on pointer conversions was reverted.

**BLOCK (pre-existing, both semantics): goose drops struct tags and does not
package-qualify unexported names.**

```go
var e any = struct{ X int `json:"a"` }{1}
_ = e.(struct{ X int `json:"b"` })
// Go: panic: interface conversion: interface {} is struct { X int "json:\"a\"" }, not struct { X int "json:\"b\"" }
```

Also `struct{ x int }` of two packages ("types from different packages").
*Fixed*: goose refuses interface conversions, assertions and type switches on
such unnamed types (`typeIdentityLost`, `checkDynamicTypes`).

**NOTE: identical Go interface types with different terms** are now stuck
(`var d interface{ M() } = c` with `c : interface{ I1 }`, then `d.(T)`).

## Round 5

**BLOCK (pre-existing, both): `error` is the term of `interface{ Error() string }`.**

```go
var e any = []error{}
_ = e.([]interface{ Error() string })
// Go: panic: interface conversion: interface {} is []error, not []interface { Error() string }
```

*Fixed*: `typeIdentityLost` counts a literal interface identical to `error`.

**BLOCK (pre-existing, both): type arguments were not checked.**

```go
type SA = struct{ X int `json:"a"` }
type SB = struct{ X int `json:"b"` }
func Box[T comparable](x T) any { return x }
func As[T any](x any) T { return x.(T) }
// As[SA](Box[SB](SB{1})) — Go: panic: interface conversion: interface {} is struct { X int "json:\"b\"" }, not struct { X int "json:\"a\"" }
```

*Fixed*: `checkInstances` (and, round 7, `checkTypeArgs` in `glangType`).

**BLOCK (pre-existing, both): a local type in a generic function is one type.**

```go
func F[T any](x any) any {
	type L struct{ X int }
	if x != nil { return x.(L) }
	return L{}
}
// F[string](F[int](nil)) — Go: panic: interface conversion: interface {} is main.L[int], not main.L[string]
```

*Fixed*: goose refuses type declarations in generic functions.

**BLOCK (coverage): composite-literal elements are converted by the
semantics**, bypassing the check (`[]any{SB{1}}`, `H{F: b}`, map literals).
*Fixed*: elements of a literal with an interface slot are checked.

**BLOCK (old semantics only): interface types are not canonical.** *Fixed in
round 8.*

```go
var y any = []interface{ error }{}
if _, ok := y.([]interface{ Error() string }); ok { panic("") }  // Go: ok = true, panics
```

goose keeps embedded interfaces as type elements, unflattened, so the two
terms differ and the old semantics' `decide (ii.ty = t)` says false. Also
`x.(interface{ io.Reader; io.Writer })` is `ok = false` for a value that
implements both (the old type-set check treats an embedded interface as one
type). Under the byte semantics both are stuck (less defined).

**REWORK: no `Convert` from a type parameter to an interface.** *Fixed in
round 7* (it was a BLOCK there).

## Round 7

**BLOCK (pre-existing, both): instantiations in type declarations were not
checked.**

```go
type SA = []interface{ Error() string }
type G[T any] struct{ v T }
func (g G[T]) Get(x any) T { return x.(T) }
type H struct{ g G[SA] }
func (h H) M(x any) { h.g.Get(x) }
// var h H; h.M([]error(nil)) — Go: panic: interface conversion: interface {} is []error, not []interface { Error() string }
```

Also `type GA = G[SA]` and promoted methods through an embedded `G[SA]`.
*Fixed*: `glangType` checks the type arguments of every instantiated named
type or alias (`checkTypeArgs`).

**BLOCK (pre-existing goose bug; wrong method under the byte semantics):
range-with-`=` and select-send stored without converting.**

```go
type I2 interface{ A() string; Error() string }
type T struct{}
func (T) A() string     { return "A" }
func (T) Error() string { return "Error" }

func Range() string { var x error; for _, x = range []I2{T{}} {}; return x.Error() }
func Sel() string {
	ch := make(chan error, 1); var i I2 = T{}
	select { case ch <- i: }
	e := <-ch; return e.Error()
}
// Go: "Error" "Error"; the model called method 0 of the (T, I2) itab: "A"
```

*Fixed*: `rangeStmt` converts an assigned key/value to an interface
variable's type, select-send converts to the channel's element type.

**BLOCK (byte semantics): no `Convert` from a type parameter.**

```go
func F[X error](x X) string { var e error = x; return e.Error() }
// F(I2(T{})) — Go: "Error"; the model: "A" (the I2 itab used as an error itab)
```

*Fixed*: `handleImplicitConversion` converts from or to a type parameter, and
between distinct interface types (also the round-7 NOTE: `type E1/E2
interface{ Error() string }` kept the E1 itab).

## Round 8 (fixes before the review)

**BLOCK (round 5's, old semantics).** *Fixed*: goose translates an interface
whose type set is a method set as its complete, flattened method set (go/types'
order), so identical interface types are one term, and type-set checks never
see an embedded interface. Constraint interfaces keep their elements.

**BLOCK (exposed by the flattening): an embedded interface's unexported
methods.** `typeIdentityLost` looked only at explicit methods and treated an
embedded named interface as package-qualified; flattened, its unexported
methods appear unqualified:

```go
// package p: type hasM interface{ m() }      package q: type hasM interface{ m() }
var e any = []interface{ p.HasM }{}   // (exported names for the embedded types)
_ = e.([]interface{ q.HasM })         // Go: panics (the two m are different methods)
```

*Fixed*: the check looks at the complete method set (negative test
`iface_embedded_unexported`).

## Round 8 (review)

**BLOCK (round 7's range fix): a named integer counter boxed as its
underlying type.**

```go
type MyInt int
func R() int { var x any; for x = range MyInt(3) {}; return x.(int) }
// Go: panic: interface conversion: interface {} is main.MyInt, not int
```

*Fixed*: `rangeVarTypes` keeps the integer's type (`types.Default` for an
untyped constant).

**BLOCK (round 7's select fix, byte semantics): a channel typed by a type
parameter.**

```go
func S[C ~chan error](ch C) string {
	var i I2 = T{}            // I2, T as in round 7
	select { case ch <- i: }
	e := <-ch; return e.Error()
}
// Go: "Error"; the model: "A"
```

*Fixed*: the element type of the channel's core type (`chanElem`).

**BLOCK: a composite literal whose type is a type parameter skipped the
element check.**

```go
type SC = struct{ X int }
type SB = struct{ X int `json:"b"` }
func Mk[C ~[]any]() C { return C{SB{1}} }
// s := Mk[[]any](); _ = s[0].(SC) — Go: panic: ... is struct { X int "json:\"b\"" }, not struct { X int }
```

*Fixed*: `hasInterfaceSlot` uses the core type.

**BLOCK (old semantics): map-literal keys were not checked.**

```go
m := map[any]int{SB{1}: 1}
for k := range m { _, ok = k.(SC) }   // Go: ok = false; the old semantics: true
```

*Fixed*: keys are checked like values.

**BLOCK (pre-existing): a local type in a package-level variable's
initializer has the term of the package-level type of the same name.**

```go
type L struct{ X int }
var Mk = func() any { type L struct{ X int }; return L{1} }
// _, ok := Mk().(L) — Go: false; both semantics: true (Mk().(L).X: Go panics)
```

*Fixed*: goose refuses local types in package-level variable initializers.

**BLOCK (old semantics; round 4's revert of round 3's restriction): pointer
reinterpretation between interface types.**

```go
var a I1 = T{1}
b := *(*I2)(&a)
_ = b.(T).x   // Go: panic: interface conversion: main.I2 is main.T, not main.T (types from different scopes)
```

The old `type_assert_step` ignores the source type (its `GoInterface` has no
static type). *Fixed for the plain-Go route*: `convert_pointer_same_underlying`
again excludes interface base types (the only route without `unsafe`: other
base types with the same underlying type have the same interface field
types).

**Inherited, not fixed (old semantics, `unsafe`): reinterpretation through
`unsafe.Pointer`.**

```go
var e error = T{1}
a := *(*any)(unsafe.Pointer(&e))
_ = a.(T).x   // Go: fatal error: runtime: name offset out of range; the old semantics: 1
```

The `unsafe.Pointer` ↔ `*T` rules (`unsafe.Semantics`) predate this branch
and are not changed by it. The byte semantics behaves as Go's memory here (it
reads the itab word as a type word, which no proof can show to be `typeAddr
T`). For the old semantics a fix needs either a static interface type in
`GoInterface` (about 35 proof files) or a deep "contains no interface" premise
on the target type (through pointers and recursive types); refusing the
rule outright breaks `strings.Builder.copyCheck`'s proof.

**NOTE (old semantics): `methodSet` is keyed by bare method names**, so a
premise `methodSet T !! "m" = some sig` for a `T` of another package than the
interface's unexported `m` reads as true but makes `x.(p.I)` succeed where Go
says `T` does not implement `p.I`. No program verifies without such a premise.
