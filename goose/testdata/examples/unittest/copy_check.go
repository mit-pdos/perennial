package unittest

type bigStruct struct {
	a, b, c int64
}

// `*p = *q` may copy between overlapping memory: goose emits CheckCopy.
func copyThroughPointers(p, q *bigStruct) {
	*p = *q
}

// x is a local variable whose address is never taken: no CheckCopy.
func copyIntoLocal(p *bigStruct) int64 {
	var x bigStruct
	x = *p
	return x.a
}

type bigStruct2 bigStruct

// A conversion that keeps the representation is still a copy from memory.
func copyConverted(p *bigStruct, q *bigStruct2) {
	*p = bigStruct(*q)
}
