// Package user accesses dep.X, whose initializer the model skips (so dep.X
// is not allocated), only where a proof can show the access is fine: taking
// its address, or loading it in a branch that is never taken.
package user

import "github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/dep"

// AddrX takes dep.X's address, which the model gives (as Go does) though the
// variable is not allocated.
func AddrX() **uint64 {
	return &dep.X
}

// LoadXIf loads dep.X and takes its address only if b; its spec requires b to
// be false, so the branch, whose load has no proof, is never taken.
func LoadXIf(b bool) uint64 {
	if b {
		v := dep.X
		p := &dep.X
		if *p != v {
			return 1
		}
		return *v
	}
	return 0
}
