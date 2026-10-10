package unittest

import "unsafe"

const GlobalConstant string = "foo"

const UntypedStringConstant = "bar" // an untyped string

const UntypedInt = 13

const OtherUntypedInt = UntypedInt + UntypedInt

const TypedInt uint64 = 32

const ConstWithArith uint64 = 4 + 3*TypedInt

const TypedInt32 uint32 = 3

const DivisionInConst uint64 = (4096 - 8) / 8

const ModInConst uint64 = 513 + 12%8 // 517

const ModInConstParens uint64 = (513 + 12) % 8 // 5

const SignedIntegerExample int64 = -37

const (
	First = iota
	Second
	Third
)

const (
	ComplicatedFirst uint64 = 2*iota + 3
	ComplicatedSecond
	ComplicatedThird
)

func useUntypedInt() uint64 {
	return UntypedInt + TypedInt
}

func useUntypedString() string {
	return UntypedStringConstant
}

type sizedStruct struct {
	a uint64
	b uint32
	c uint16
}

// unsafe.Sizeof, Offsetof and Alignof are constants (gc's layout); a uintptr
// constant is a 64-bit word.
const SizeofSized = unsafe.Sizeof(sizedStruct{})

const OffsetofC uintptr = unsafe.Offsetof(sizedStruct{}.c)

func sizeofLocal() int {
	return int(unsafe.Sizeof(uint32(0))) + int(unsafe.Alignof(sizedStruct{}))
}
