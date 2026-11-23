// Package gomodel is the Go models' choice and stuck points: a package that
// the overlay adds to the standard library (Perennial/Code/internal/gomodel.toml,
// replaces = ["*"]), so that a model of a standard-library package, which
// cannot import goose-lang/primitive, can state each nondeterministic choice
// and each point where it has no behaviour as a visible call. Each function
// is a primitive stub: its GooseLang model is in
// Perennial/TrustedCode/internal/gomodel.lean, and the Go body here only
// serves gc builds and differential tests, taking the common case.
package gomodel

// Choose is an arbitrary boolean (GooseLang: any). In Go it is false.
func Choose() bool {
	return false
}

// ChooseUint64 is an arbitrary uint64 (GooseLang: any). In Go it is 0.
func ChooseUint64() uint64 {
	return 0
}

// Stuck has no behaviour (GooseLang: stuck, so a verified program never
// calls it, and a model calls it only where it gives Go's behaviour up). In
// Go it panics, so that a test that reaches it fails.
func Stuck() {
	panic("gomodel.Stuck: the model has no behaviour here")
}
