package unsafe_stack_map

import "unsafe"

// unsafe.Pointer(uintptr(p) + off) is translated only when nothing in it can move the
// goroutine's stack: a map index calls the runtime.

func offsetWithMapIndex(a *[4]int64, m map[int]uintptr) unsafe.Pointer {
	return unsafe.Pointer(uintptr(unsafe.Pointer(&a[0])) + m[0]) // ERROR unsafe.Pointer(uintptr(p) + offset) with an offset that may move the stack
}
