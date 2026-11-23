package unittest

import "github.com/goose-lang/primitive"

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

func ResolveEvents(x uint64) {
	p := primitive.NewProph()
	p.ResolveU64(x)
	p.Resolve(prophEvent{kind: 1, val: x})
	p.Resolve(x)
}
