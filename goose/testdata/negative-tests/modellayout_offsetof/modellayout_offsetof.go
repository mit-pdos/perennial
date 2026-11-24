// Package modellayout_offsetof takes, in an array length, an offset in a
// struct that contains a type that a Go model gives another layout.
package modellayout_offsetof

import (
	"unsafe"

	"github.com/mit-pdos/perennial/goose/testdata/negative-tests/modellayout_offsetof/dep"
)

type W struct {
	ts [2]dep.T
	X  uint64
}

func F() uint64 {
	var a [unsafe.Offsetof(W{}.X)]byte // ERROR unsafe.Offsetof of a type containing github.com/mit-pdos/perennial/goose/testdata/negative-tests/modellayout_offsetof/dep.T
	return uint64(len(a))
}
