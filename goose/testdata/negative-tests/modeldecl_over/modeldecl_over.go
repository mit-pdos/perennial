// Package modeldecl_over declares a type over a type whose layout a Go model
// changes (here a trusted type, whose Lean definition may differ from Go's):
// Go gives M the underlying type of the real dep.T (a struct), the translation
// that of dep.T's model, and go.layoutModelled lists dep.T but not M.
package modeldecl_over

import "github.com/mit-pdos/perennial/goose/testdata/negative-tests/modeldecl_over/dep"

type M dep.T // ERROR type M declared over github.com/mit-pdos/perennial/goose/testdata/negative-tests/modeldecl_over/dep.T

// M2 is declared over M, so over dep.T too.
type M2 M
