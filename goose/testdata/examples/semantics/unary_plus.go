package semantics

// Unary `+` is the identity at every integer and float type (the Go spec: `+x` is `0 + x`).

func testUnaryPlusInt() bool {
	var i int = -3
	var i64 int64 = -1 << 62
	var i32 int32 = -7
	var i16 int16 = 300
	var i8 int8 = -128
	var u uint = 5
	var u64 uint64 = 1<<64 - 1
	var u32 uint32 = 1<<32 - 1
	var u16 uint16 = 9
	var u8 uint8 = 255
	var up uintptr = 17
	return +i == -3 && +i64 == -1<<62 && +i32 == -7 && +i16 == 300 && +i8 == -128 &&
		+u == 5 && +u64 == 1<<64-1 && +u32 == 1<<32-1 && +u16 == 9 && +u8 == 255 && +up == 17
}

type plusNamed int64

func testUnaryPlusUntypedAndNamed() bool {
	one := +1
	var n plusNamed = -4
	return one == 1 && +n == -4
}

func testUnaryPlusFloat() bool {
	f := 1.5
	var f32 float32 = -2.25
	g := +0.5
	return +f == 1.5 && +f32 == -2.25 && g == 0.5
}
