// Package dep is imported by filteredimport, whose configuration does not
// import it.
package dep

type X struct{}

// constants a translation that does not import dep still uses: by their values
const N uint64 = 3

const Untyped = 1 << 40

type Kind uint32

const KindB Kind = 2
