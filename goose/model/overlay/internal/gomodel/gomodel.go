// Package gomodel is the Go models' choice, stuck and read-lock points: a
// package that the overlay adds to the standard library
// (Perennial/Code/internal/gomodel.toml, replaces = ["*"]), so that a model of
// a standard-library package, which cannot import goose-lang/primitive, can
// state each nondeterministic choice, each point where it has no behaviour and
// each cell it makes read-only as a visible call. Each function is a primitive
// stub: its GooseLang model is in Perennial/TrustedCode/internal/gomodel.lean,
// and the Go body here only serves gc builds and differential tests, taking
// the common case.
package gomodel

// Choose is an arbitrary boolean (GooseLang: any). In Go it is false.
func Choose() bool {
	return false
}

// ChooseUint64 is an arbitrary uint64 (GooseLang: any). In Go it is 0.
func ChooseUint64() uint64 {
	return 0
}

// Stuck has no behaviour: a model calls it where it does not model Go's
// behaviour (it is less defined than Go there, never more). GooseLang: the
// stuck Panic "not modelled", which recover cannot catch and which no WP
// rule steps, so a verified program never reaches a call. (A model that
// blocked forever instead would be unsound for this: a select with no cases
// has a WP with precondition True, which proves anything after it.) In Go it
// blocks forever.
func Stuck() {
	select {}
}

// StartRead makes *p read-only from here on: GooseLang leaves a reader on the
// heap cell at p for good (StartRead with no FinishRead), so later loads of
// that cell step and stores to it are stuck (the model is less defined than
// Go there, never more). It marks the cell only: for a T stored in several
// cells (a struct, an array), the others are unaffected. A model calls it where
// Go shares memory that the model copies (strings.Builder.String's buffer), so
// that a later write Go would make visible through the sharing is stuck in the
// model instead. In Go it does nothing.
func StartRead[T any](p *T) {
}
