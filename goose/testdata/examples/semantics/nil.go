package semantics

import "unsafe"

func testUnsafePointerNil() bool {
	var p unsafe.Pointer
	q := unsafe.Pointer(nil)
	x := new(uint64)
	r := unsafe.Pointer(x)
	return p == nil && q == nil && p == q && r != nil
}

func testCompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func testComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

func testCompareNilToNil() bool {
	s := new(*uint64)
	return *s == nil
}

func testComparePointerWrappedToNil() bool {
	var s []byte
	s = make([]byte, 1)
	return s != nil
}

func testComparePointerWrappedDefaultToNil() bool {
	var s []byte
	return s == nil
}

func testInterfaceNilWithType() bool {
	// subtlety in Go: nil interface vs interface with a nil pointer in it are
	// different
	var isNil any = nil
	var notNil any = (*string)(nil)
	return isNil == nil && notNil != nil && isNil != notNil
}
