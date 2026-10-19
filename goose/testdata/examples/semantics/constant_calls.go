package semantics

import "unsafe"

func testConstantCalls() bool {
	var x uint64
	var a [3]uint64
	n := unsafe.Sizeof(x)
	m := len(a)
	return n == 8 && m == 3
}
