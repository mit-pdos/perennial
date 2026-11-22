package semantics

// helpers

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func stringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func byteSliceToString(p []byte) string {
	// must be lifted, impure operation
	return string(p)
}

// tests
func testStringToBytesEmptyNonNil() bool {
	return stringToByteSlice("") != nil
}

func testByteSliceToString() bool {
	x := make([]byte, 3)
	x[0] = 65
	x[1] = 66
	x[2] = 67
	return byteSliceToString(x) == "ABC"
}

func testByteToString() bool {
	var a, c byte = 65, 200
	return string(a) == "A" && string(c) == "\xc3\x88"
}

const slashRune = '/'

func testUntypedRuneConst() bool {
	var c byte = 'a'
	return slashRune == '/' && c-('a'-'A') == 'A' &&
		string(slashRune) == "/" && string('é') == "\xc3\xa9" &&
		string(0xD800+0*slashRune) == "\xef\xbf\xbd" && string(-1+0*slashRune) == "\xef\xbf\xbd"
}

const negUnderflowConst = -1e-400

// a constant is never a negative zero: one that rounds to zero converts to +0
func testNegUnderflowConstIsPosZero() bool {
	const local = -1e-50
	x := negUnderflowConst
	var y float32 = negUnderflowConst
	var z float32 = local
	w := -1e-400
	return 1/x > 0 && 1/y > 0 && 1/z > 0 && 1/w > 0
}

func testUntypedIntToFloat64() bool {
	var x float64 = -1
	var y float64 = -1
	return x == y
}

// float32(n) of every integer type, and of an untyped integer constant: the exact integer
// rounded once to binary32. 2^24+1 is halfway between 2^24 and 2^24+2 and rounds to even
// (2^24); 2^24+3 rounds to 2^24+4.
func testIntToFloat32() bool {
	var i8 int8 = -128
	var u8 uint8 = 255
	var i16 int16 = -32768
	var u16 uint16 = 65535
	var i32 int32 = 16777217
	var u32 uint32 = 16777219
	var i64 int64 = -16777217
	var u64 uint64 = 16777217
	var i int = 16777217
	var u uint = 16777217
	var p uintptr = 16777217
	var c float32 = 16777217
	var d float32 = -16777217
	return float32(i8) == -128 && float32(u8) == 255 &&
		float32(i16) == -32768 && float32(u16) == 65535 &&
		float32(i32) == float32(i32-1) && float32(u32) == float32(u32+1) &&
		float32(i64) == -16777216 && float32(u64) == 16777216 &&
		float32(i) == 16777216 && float32(u) == 16777216 && float32(p) == 16777216 &&
		c == 16777216 && d == -16777216
}

// float64(n) of every integer type, and of an untyped integer constant: the exact integer
// rounded once to binary64. 2^53+1 rounds to 2^53; 2^53+3 to 2^53+4.
func testIntToFloat64() bool {
	var i8 int8 = -128
	var u8 uint8 = 255
	var i16 int16 = -32768
	var u16 uint16 = 65535
	var i32 int32 = -2147483648
	var u32 uint32 = 4294967295
	var i64 int64 = 9007199254740993
	var u64 uint64 = 9007199254740995
	var i int = -9007199254740993
	var u uint = 9007199254740993
	var p uintptr = 9007199254740993
	var c float64 = 9007199254740993
	var d float64 = -9007199254740993
	return float64(i8) == -128 && float64(u8) == 255 &&
		float64(i16) == -32768 && float64(u16) == 65535 &&
		float64(i32) == -2147483648 && float64(u32) == 4294967295 &&
		float64(i64) == float64(i64-1) && float64(u64) == float64(u64+1) &&
		float64(i) == -9007199254740992 && float64(u) == 9007199254740992 &&
		float64(p) == 9007199254740992 &&
		c == 9007199254740992 && d == -9007199254740992
}
