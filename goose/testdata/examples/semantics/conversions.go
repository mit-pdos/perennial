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

const offTieConst = 1 + 0x1p-24 + 0x1p-60

type float32Box struct {
	f float32
}

func float32Id(x float32) float32 {
	return x
}

// a constant converted to float32 is rounded once, from its exact value: Go
// gives 1+0x1p-23 (just above the tie between 1 and 1+0x1p-23), not the
// float32 rounding of its float64 rounding 1+0x1p-24 (an exact tie, which
// rounds to even, 1); -1e-50 rounds to +0
func testFloat32ConstRoundsOnce() bool {
	const typed float32 = 1 + 0x1p-24 + 0x1p-60
	var a float32 = offTieConst
	b := float32(1 + 0x1p-24 + 0x1p-60)
	box := float32Box{f: offTieConst}
	arr := [1]float32{offTieConst}
	var z float32 = -1e-50
	one := float32(1)
	return typed == 1+0x1p-23 && a == 1+0x1p-23 && b == 1+0x1p-23 &&
		box.f == 1+0x1p-23 && arr[0] == 1+0x1p-23 && float32Id(offTieConst) == 1+0x1p-23 &&
		a-1 == 0x1p-23 && one+(0x1p-24+0x1p-60) == 1 && 1/z > 0 && 1/float32Id(-1e-50) > 0
}
