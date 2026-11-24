package unittest

import (
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/perennial/proph"
)

func Oracle() {
	p := primitive.NewProph()
	p = p
}

type typing struct {
	proph primitive.ProphId
}

type prophEvent struct {
	kind uint64
	val  uint64
}

// ResolveEvents uses github.com/mit-pdos/perennial/proph, Perennial's package
// of prophecy variables, including Resolve, which resolves with an interface value.
func ResolveEvents(x uint64) {
	p := proph.NewProph()
	p.ResolveBool(x == 0)
	p.ResolveU64(x)
	p.Resolve(prophEvent{kind: 1, val: x})
	p.Resolve(x)
}
