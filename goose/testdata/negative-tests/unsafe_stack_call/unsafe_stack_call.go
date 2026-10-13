package unsafe_stack_call

import "unsafe"

// unsafe.Pointer(uintptr(p) + off) is translated only when nothing in it can move the
// goroutine's stack: a call may.

func off() uintptr { return 8 }

func offsetWithCall(a *[4]int64) unsafe.Pointer {
	return unsafe.Pointer(uintptr(unsafe.Pointer(&a[0])) + off()) // ERROR unsafe.Pointer(uintptr(p) + offset) with an offset that may move the stack
}
