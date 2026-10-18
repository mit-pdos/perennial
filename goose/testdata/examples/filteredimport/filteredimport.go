// Package filteredimport is translated with a configuration that filters out
// its import of dep (filteredimport/github_com/.../filteredimport.toml), so its
// translation cannot name dep's types: goose must not write them where the
// source does not name them either (method sets, the methods of embedded
// interfaces).
package filteredimport

import "github.com/mit-pdos/perennial/goose/testdata/examples/filteredimport/dep"

// a method set entry whose signature mentions dep.X: `(id, none)`
type T struct{ n uint64 }

func (T) Use(x *dep.X) {}

func (t *T) Get() uint64 { return t.n }

// not translatable as a type (its method mentions dep.X): axiomatized
type withDep interface {
	Use(x *dep.X)
	Get() uint64
}

// embeds withDep: Get is written out, Use (which mentions dep.X) is not, and
// withDep stays a type term (whose membership the semantics leaves unspecified)
type Getter interface {
	withDep
	Close()
}

// embeds an interface all of whose methods can be written: flattened
type plain interface{ Get() uint64 }

type PlainCloser interface {
	plain
	Close()
}

// embeds an interface literal that embeds withDep: Get is written out, and the
// literal stays a type term (written as Get and the type term withDep)
type litGetter interface {
	interface{ withDep }
	Close()
}
