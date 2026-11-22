// Package dep declares aliases under every action of its configuration
// (dep/github_com/.../xpkgalias/dep.toml, and the same in Perennial/Code):
// translated, axiomatized and trusted. Each has a reducible descriptor,
// `A.ty`, defined as the descriptor of the type it denotes.
package dep

import (
	"sync"

	"github.com/mit-pdos/perennial/goose/testdata/examples/xpkgalias/dep2"
)

type X struct{ n uint64 }

// translated
type A = X

// axiomatized: an alias of a type of a package xpkgalias does not import
type L = dep2.Y

// axiomatized: the configuration does not import sync, so its descriptor is
// spelled out
type M = sync.Mutex

// axiomatized and generic
type G[T any] = dep2.Box[T]

// trusted
type Tr = *X

// axiomatized: an alias of an alias declared later, written as the type it
// denotes
type PtrLater = *Later

type Later = A

// axiomatized, and goose cannot translate what it denotes (a struct tag on an
// unnamed struct type): its descriptor is opaque
type Tagged = struct {
	f uint64 `json:"f"`
}
