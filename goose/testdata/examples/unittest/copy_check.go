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

type bigTagged struct {
	a    int64 `json:"a"`
	b, c int64
}

// Conversions that ignore struct tags keep the representation too.
func copyTagConverted(p *bigStruct, q *bigTagged) {
	*p = bigStruct(*q)
}

type innerBig struct{ x bigStruct }

type outerBig struct {
	*innerBig
	y bigStruct
}

// p.x is in *p.innerBig, another object than p.y: CheckCopy.
func copyPromoted(p *outerBig) {
	p.x = p.y
}

type ptrLike interface{ ~*bigStruct | ~*bigStruct2 }

// The conversion between type parameters is kept, after the CheckCopy.
func copyTypeParamConv[T, U ptrLike](p *T, q *U) {
	*p = T(*q)
}
