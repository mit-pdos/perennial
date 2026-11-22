// Package skip_cross_load refers to a variable that its package skips.
package skip_cross_load

import "github.com/mit-pdos/perennial/goose/testdata/negative-tests/skip_cross_load/dep"

func F() uint64 {
	return dep.X // ERROR skipped variable github.com/mit-pdos/perennial/goose/testdata/negative-tests/skip_cross_load/dep.X (skip: "a constant: cannot panic, no effect beyond the variable") is referenced by translated F
}
