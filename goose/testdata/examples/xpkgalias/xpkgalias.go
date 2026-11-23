// Package xpkgalias has struct types whose fields have the types of aliases
// of another package (dep), translated or not there: an alias always has a
// descriptor, so the field's go.type is the alias's descriptor, and its Lean
// type the type it denotes, named in the package that declares it.
package xpkgalias

import "github.com/mit-pdos/perennial/goose/testdata/examples/xpkgalias/dep"

// an alias of another package's alias
type C = dep.A

// translated: L denotes dep2.Y, of a package this one does not import, but
// only under a pointer, where the go.type (dep.L.ty) is needed
type withAliases struct {
	a dep.A
	c C
	p *dep.L
	g []dep.G[uint64]
	m *dep.M
	t dep.Tr
}

// axiomatized: the Lean type of dep.L's values is dep2.Y's, and this package
// does not import dep2
type withAxiomatizedAlias struct {
	l dep.L
}

func useAliases(w withAliases, l *dep.L) uint64 {
	_ = w
	_ = l
	return 0
}
