// Package modellayout_sizeof takes the size of a type that a Go model gives
// another layout: Go's constant is gc's size of the real type (16), not the
// model's (8).
package modellayout_sizeof

import (
	"unsafe"

	"github.com/mit-pdos/perennial/goose/testdata/negative-tests/modellayout_sizeof/dep"
)

const n = unsafe.Sizeof(dep.T{}) // ERROR unsafe.Sizeof of a type containing github.com/mit-pdos/perennial/goose/testdata/negative-tests/modellayout_sizeof/dep.T

func F() uintptr {
	return n
}
