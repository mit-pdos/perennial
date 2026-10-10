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
