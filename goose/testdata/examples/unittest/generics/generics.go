package generics

import (
	"github.com/mit-pdos/perennial/goose/testdata/examples/unittest/generics/helpers"
)

// Box is the simplest generic struct
type Box[T any] struct {
	Value T
}

// BoxGet is a function getter (rather than a method)
func BoxGet[T any](b Box[T]) T {
	return b.Value
}

func BoxGet2(b Box[uint64]) uint64 {
	return b.Value
}

func (b Box[T]) Get() T {
	return b.Value
}

func makeGenericBox[T any](value T) Box[T] {
	return Box[T]{Value: value}
}

func makeBox() Box[uint64] {
	// Go requires this syntactic type instantiation
	return Box[uint64]{Value: 42}
}

func useBoxGet() uint64 {
	x := makeGenericBox(uint64(42))
	return x.Get()
}

type Container[T any] struct {
	// various uses of T inside a type
	X T
	Y map[int]T
	Z *T
	W uint64
}

func useContainer() {
	container := Container[uint64]{X: 1, Y: map[int]uint64{1: 2}, Z: new(uint64), W: 3}
	container.X = 2
	container.Y[2] = 3
	container.Z = new(uint64)
	container.W = 4
}

// B does not have type parameters but requires instantiating a generic type
type UseContainer struct {
	X Container[uint64]
}

// OnlyIndirect can be modeled as a go_type without its type argument (due to
// the indirections)
type OnlyIndirect[T any] struct {
	X []T
	Y *T
}

// type IntMap[T any] map[uint64]T

// MultiParam takes two type parameters
type MultiParam[A any, B any] struct {
	Y B
	X A
}

func useMultiParam() {
	mp := MultiParam[uint64, bool]{Y: true, X: 1}
	mp.X = 2
}

func swapMultiParam[A any](p *MultiParam[A, A]) {
	temp := p.X
	p.X = p.Y
	p.Y = temp
}

func multiParamFunc[A any, B any](x A, b B) []B {
	return []B{b}
}

func useMultiParamFunc() {
	multiParamFunc[uint64, bool](1, true)
	// XXX: _ needed to work around goose bug
	return
}

func useAnyPointer() {
	var x uint64
	helpers.AnyPointer(&x)
}

type nonStructGeneric[T any] []T

type useNonStructGeneric[T any] struct {
	x nonStructGeneric[T]
}
