// Package skip_cross_addr refers to a variable that its package skips.
package skip_cross_addr

import "github.com/mit-pdos/perennial/goose/testdata/negative-tests/skip_cross_addr/dep"

func F() *uint64 {
	return &dep.X // ERROR skipped variable github.com/mit-pdos/perennial/goose/testdata/negative-tests/skip_cross_addr/dep.X
}
