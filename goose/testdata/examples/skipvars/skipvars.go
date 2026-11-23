// Package skipvars has package variables that goose does not translate (the
// `skip` entries of its config,
// github_com/mit_pdos/perennial/goose/testdata/examples/skipvars.toml), between
// translated ones: the translation has no name, allocation or initialization
// step for a skipped variable, keeps the translated initializers in Go's
// order, and lists the skipped variables in skipped'.
package skipvars

type T struct{ n uint64 }

type I interface{ Get() uint64 }

func (t *T) Get() uint64 { return t.n }

// translated, initialized first
var first = uint64(1)

// skipped: newX only allocates
var X = newX()

func newX() *uint64 {
	v := uint64(42)
	return &v
}

// translated, initialized after X in Go
var mid = first + 1

// skipped: one initializer of two variables
var a, b = pair()

func pair() (uint64, uint64) { return 1, 2 }

// skipped: no initializer
var Z T

// skipped: blank variables (interface checks)
var _ I = (*T)(nil)
var _ = T{}

// translated, initialized last
var last = mid + 1

// Last is translated: it reads only translated variables.
func Last() uint64 {
	return last
}

// skipped: a long initializer, listed in skipped' cut short with a hash of
// the whole declaration
var table = [12]uint64{1000000001, 1000000002, 1000000003, 1000000004, 1000000005, 1000000006, 1000000007, 1000000008, 1000000009, 1000000010, 1000000011, 1000000012}
