// Package xpkgalias has struct types whose fields have the types of aliases
// of another package (dep). goose translates such a struct when dep's own
// translation (with its configuration in the same configuration directory)
// translates the alias: the field's go.type is the alias's descriptor, and its
// Lean type the type it denotes, named in the package that declares it.
package xpkgalias

import "github.com/mit-pdos/perennial/goose/testdata/examples/xpkgalias/dep"

// translated: dep translates A and L (L denotes dep2.Y, of a package this one
// does not import)
type withAliases struct {
	a dep.A
	l dep.L
	p *dep.L
}

// axiomatized: dep does not translate M
type withUntranslatedAlias struct {
	m dep.M
}

func useAliases() uint64 {
	var w withAliases
	_ = w
	return 0
}
