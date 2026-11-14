/-
`errors.As`'s spec, assumed (`As` finds the target's type by reflection, which is not
translated; see the spec's docstring).
-/
module

public import Perennial.Spec.errors.As

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- Axiom: `As` and `as` use reflection throughout, which is not translated.

Why the first-match case (`AsFirst`) is sound: Go's `as` (`errors/wrap.go`) begins its loop with

```go
if reflectlite.TypeOf(err).AssignableTo(targetType) {
	targetVal.Elem().Set(reflectlite.ValueOf(err))
	return true
}
```

before the `As` method or any `Unwrap`, and `As` reaches it after its panics (excluded by
`AsTarget T` and `l ↦ v`) when `err ≠ nil`. A type is assignable to itself, and to an interface
type it implements. A Go check (go1.27.3), every method of the errors panicking:

```go
type trap struct{ n int }
func (t *trap) Error() string        { panic("Error called") }
func (t *trap) Unwrap() error        { panic("Unwrap called") }
func (t *trap) As(target any) bool   { panic("As called") }
func (t *trap) Is(target error) bool { panic("Is called") }

type timeouter interface{ Timeout() bool }
type terr struct{}
func (terr) Error() string { return "t" }
func (terr) Timeout() bool { return true }
func (terr) Unwrap() error { panic("Unwrap called") }

e := &trap{1}; var t *trap
errors.As(error(e), &t), t == e                                  // true true
le := &os.LinkError{Op: "rename", Old: "a", New: "b"}; var target *os.LinkError
errors.As(error(le), &target), target == le                      // true true
var to timeouter
errors.As(error(terr{}), &to), to == timeouter(terr{})           // true true
```
-/
axiom errors.As.wp_proof : errors.As.spec (GF := GF) (hG := hG)

end proof

end Perennial
