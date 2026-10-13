package proph_type_arg

import "github.com/goose-lang/primitive"

// A ProphId substituted for a type parameter would reach a struct field (gc's ProphId is
// 0 bytes, the model's is not).

type Box[T any] struct {
	a T
	b uint64
}

var x Box[primitive.ProphId] // ERROR a ProphId in a type argument
