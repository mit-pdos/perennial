// Package dep declares aliases that xpkgalias's struct types use. Its
// configuration in xpkgalias's configuration directory
// (xpkgalias/github_com/.../xpkgalias/dep.toml) translates A and L, not M.
package dep

import (
	"sync"

	"github.com/mit-pdos/perennial/goose/testdata/examples/xpkgalias/dep2"
)

type X struct{ n uint64 }

// translated: an alias of this package's struct
type A = X

// translated: an alias of a type of a package xpkgalias does not import
type L = dep2.Y

// not translated: dep's configuration does not import sync
type M = sync.Mutex
