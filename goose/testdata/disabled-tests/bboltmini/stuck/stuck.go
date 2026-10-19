// Package stuck holds the constructs next to bboltmini's that the model must
// NOT verify: for each test function here, {{ True }} testX() {{ RET true }}
// must be unprovable. Some return true in Go but use something the model
// leaves stuck on purpose (bbolt's original uintptr forms, float bits, padded
// structs); the others return true in the model only if the semantics is
// unsound (Go returns false, or either answer).
package stuck

import (
	"sync/atomic"
	"unsafe"
)

type Pgid uint64

type leafPageElement struct {
	flags uint32
	pos   uint32
	ksize uint32
	vsize uint32
}

// bbolt's own UnsafeAdd (internal/common/unsafe.go:7): uintptr back to a
// pointer stays stuck. True in Go.
func unsafeAdd(base unsafe.Pointer, offset uintptr) unsafe.Pointer {
	return unsafe.Pointer(uintptr(base) + offset)
}

func testOriginalUnsafeAdd() bool {
	buf := make([]byte, 16)
	*(*uint64)(unsafeAdd(unsafe.Pointer(&buf[0]), 8)) = 5
	return buf[8] == 5
}

// bbolt's own pos (internal/common/inode.go:87): uintptr(p) is known only
// modulo 8 (or not at all), so the difference is unknown. True in Go.
func testOriginalPos() bool {
	buf := make([]byte, 4096)
	elem := (*leafPageElement)(unsafe.Add(unsafe.Pointer(&buf[0]), 16))
	b := buf[64:70]
	pos := uint32(uintptr(unsafe.Pointer(&b[0])) - uintptr(unsafe.Pointer(elem)))
	return pos == 48
}

// unsafe.Add one past the end of the allocation is invalid. True in Go.
func testAddPastEnd() bool {
	buf := make([]byte, 16)
	return unsafe.Add(unsafe.Pointer(&buf[0]), len(buf)) != nil
}

// unsafe.Slice past the allocation, then an access there. Go reads whatever
// follows; the model has no cell.
func testSlicePastEnd() bool {
	buf := make([]byte, 16)
	s := unsafe.Slice(&buf[0], 32)
	return s[20] == s[20]
}

// A pointer read out of bytes. True in Go (zero bytes are nil).
func testPointerFromBytes() bool {
	buf := make([]byte, 8)
	return *(**int)(unsafe.Pointer(&buf[0])) == nil
}

// Bytes written over a pointer. True in Go.
func testBytesOverPointer() bool {
	x := new(int)
	*(*uint64)(unsafe.Pointer(&x)) = 0
	return x == nil
}

// A float's bits: floats are not plain. True in Go.
func testFloatBits() bool {
	f := 1.0
	return *(*uint64)(unsafe.Pointer(&f)) == 0x3FF0000000000000
}

// A padded struct is not plain, so it has no byte view. True in Go.
type padded struct {
	a uint8
	b uint64
}

func testPaddedView() bool {
	buf := make([]byte, 16)
	buf[8] = 7
	return (*padded)(unsafe.Pointer(&buf[0])).b == 7
}

// An atomic at an address that is not 8-aligned in some executions: a []byte
// is only 1-aligned. Go: works, tears, or faults, depending on the address and
// the CPU.
func testMisalignedAtomic() bool {
	buf := make([]byte, 16)
	return atomic.AddInt64((*int64)(unsafe.Pointer(&buf[1])), 1) == 1
}

// Go promises a []byte nothing beyond 1-alignment.
func testByteSliceAligned() bool {
	buf := make([]byte, 16)
	return uintptr(unsafe.Pointer(&buf[0]))%8 == 0
}

// A plain field of a non-plain struct at gc offset 12: its address is 4 mod 8
// in Go, so this is false in Go.
type mixed struct {
	x uint64
	z uint32
	y uint32
	p *int
}

func testFieldResidue() bool {
	s := &mixed{}
	return uintptr(unsafe.Pointer(&s.y))%8 == 0
}

// Pointers to distinct zero-size variables may be equal. gc gives every
// zero-size heap object the same address, so this is false in Go once p and q
// escape (and true when they stay on the stack).
var sinkP, sinkQ *[0]uint64

func testZeroSizeDistinct() bool {
	p, q := new([0]uint64), new([0]uint64)
	sinkP, sinkQ = p, q
	return p != q
}

// A whole-struct copy between partially overlapping views. gc copies forward
// in 16-byte chunks: the buffer becomes 0 0 1 1 3 3 5 5 7 9, not memmove's
// 0 0 1 2 3 4 5 6 7 9, so this is false in Go.
type meta struct{ a, b, c, d, e, f, g, h uint64 }

//go:noinline
func copyMeta(dst, src *meta) { *dst = *src }

func testOverlappingCopy() bool {
	buf := make([]uint64, 16)
	for i := range buf {
		buf[i] = uint64(i)
	}
	copyMeta((*meta)(unsafe.Pointer(&buf[1])), (*meta)(unsafe.Pointer(&buf[0])))
	return buf[3] == 2
}
