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
