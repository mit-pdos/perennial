package unittest

import "unsafe"

// unsafe.Pointer(uintptr(p) + offset) is unsafe.Add(p, offset).
func unsafeAddPattern(p unsafe.Pointer, n uintptr) unsafe.Pointer {
	return unsafe.Pointer(uintptr(p) + n + 8)
}

func unsafeAddCall(p unsafe.Pointer, n int) unsafe.Pointer {
	return unsafe.Add(p, n)
}

func unsafeSliceCall(p *uint64, n int) []uint64 {
	return unsafe.Slice(p, n)
}

func unsafeAddr(p unsafe.Pointer) uintptr {
	return uintptr(p)
}

// The distance between two pointers, in one expression.
func unsafePtrDiff(b []byte, p unsafe.Pointer) uint32 {
	return uint32(uintptr(unsafe.Pointer(&b[0])) - uintptr(p))
}

type unsafeHeader struct {
	id    uint64
	flags uint16
	count uint16
}

func unsafeSizes() (uintptr, uintptr, uintptr) {
	var h unsafeHeader
	return unsafe.Sizeof(h), unsafe.Offsetof(h.count), unsafe.Alignof(h)
}

func unsafeIncUintptr(u uintptr) uintptr {
	u++
	return u
}

// Slicing a pointer to an array (bbolt's UnsafeByteSlice).
func sliceArrayPtr(p *[16]byte, i, j int) []byte {
	return p[i:j:j]
}

func sliceArrayPtr2(p *[16]byte) []byte {
	return p[2:]
}

// bbolt's unsafeByteSlice: a pointer to an array larger than the allocation, sliced; only
// the max elements are accessed (unsafe.ArraySlice).
func unsafeByteSlice(base unsafe.Pointer, offset uintptr, i, j int) []byte {
	return (*[0x7FFFFFFF]byte)(unsafe.Add(base, offset))[i:j:j]
}
