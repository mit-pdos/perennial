// Package rejected holds the whole copies that goose must refuse to
// translate: the semantics copies a struct or array by value, but gc copies
// with a Move that is wrong when the two sides partially overlap
// (docs/design/unsafe-memory.md, R4). goose's guard reports each line marked
// "// refused", and nothing else. Most return false in Go and would return
// true under value semantics; testOverlappingArrayCopy is true in Go, but the
// guard cannot tell it from testArrayFieldOverlapCopy (deliberately
// incomplete).
package rejected

import "unsafe"

type meta struct{ a, b, c, d, e, f, g, h uint64 }

// counting is a buffer of 16 words holding 0 to 15.
func counting() []uint64 {
	buf := make([]uint64, 16)
	for i := range buf {
		buf[i] = uint64(i)
	}
	return buf
}

// A whole-struct copy between partially overlapping views. gc copies forward
// in 16-byte chunks: the buffer becomes 0 0 1 1 3 3 5 5 7 9, not memmove's
// 0 0 1 2 3 4 5 6 7 9, so this is false in Go.
//
//go:noinline
func copyMeta(dst, src *meta) {
	*dst = *src // refused
}

func testOverlappingCopy() bool {
	buf := counting()
	copyMeta((*meta)(unsafe.Pointer(&buf[1])), (*meta)(unsafe.Pointer(&buf[0])))
	return buf[3] == 2
}

// Overlapping plain arrays in safe Go (slice-to-array-pointer conversions):
// gc copies *p = *q with memmove, so this is true in Go. The guard cannot tell
// this copy from dst.A = src.A below, so goose refuses it: deliberately
// incomplete.
func testOverlappingArrayCopy() bool {
	s := counting()
	*(*[8]uint64)(s[1:9]) = *(*[8]uint64)(s[0:8]) // refused
	return s[3] == 2
}

// An array field copied between overlapping views: gc uses a Move, not
// memmove, so buf[4] is 2, not value semantics' 3, and this is false in Go.
type withArray struct {
	H uint64
	A [8]uint64
}

//go:noinline
func copyArrayField(dst, src *withArray) {
	dst.A = src.A // refused
}

func testArrayFieldOverlapCopy() bool {
	buf := counting()
	copyArrayField((*withArray)(unsafe.Pointer(&buf[1])), (*withArray)(unsafe.Pointer(&buf[0])))
	return buf[4] == 3
}

// The next three copy between places whose bases are two pointers or slices
// loaded from memory. They look like copies inside one object, but the loaded
// pointers point at overlapping views, and gc gives the chunked result for
// each, so each is false in Go.
type twoPointers struct{ x, y *meta }

//go:noinline
func copyViaPointerFields(pr *twoPointers) {
	*pr.y = *pr.x // refused
}

func testCopyViaPointerFields() bool {
	buf := counting()
	copyViaPointerFields(&twoPointers{
		x: (*meta)(unsafe.Pointer(&buf[0])),
		y: (*meta)(unsafe.Pointer(&buf[1])),
	})
	return buf[3] == 2
}

type twoSlices struct{ a, b []meta }

//go:noinline
func copyViaSliceFields(s *twoSlices) {
	s.b[0] = s.a[0] // refused
}

func testCopyViaSliceFields() bool {
	buf := counting()
	copyViaSliceFields(&twoSlices{
		a: unsafe.Slice((*meta)(unsafe.Pointer(&buf[0])), 1),
		b: unsafe.Slice((*meta)(unsafe.Pointer(&buf[1])), 1),
	})
	return buf[3] == 2
}

//go:noinline
func copyViaNestedSlices(x [][]meta) {
	x[1][0] = x[0][0] // refused
}

func testCopyViaNestedSlices() bool {
	buf := counting()
	copyViaNestedSlices([][]meta{
		unsafe.Slice((*meta)(unsafe.Pointer(&buf[0])), 1),
		unsafe.Slice((*meta)(unsafe.Pointer(&buf[1])), 1),
	})
	return buf[3] == 2
}
