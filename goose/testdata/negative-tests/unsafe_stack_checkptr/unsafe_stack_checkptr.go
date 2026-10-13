package unsafe_stack_checkptr

import "unsafe"

// A conversion from unsafe.Pointer to a pointer is a runtime call (checkptrAlignment) in a
// build with checkptr (-race), which may move the stack.

func offsetWithConversion(a *[4]int64, p unsafe.Pointer) unsafe.Pointer {
	return unsafe.Pointer(uintptr(unsafe.Pointer((*int64)(p))) + 8) // ERROR unsafe.Pointer(uintptr(p) + offset) with a p that may move the stack
}
