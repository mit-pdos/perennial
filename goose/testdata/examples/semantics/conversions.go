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
func testByteSliceToString() bool {
	x := make([]byte, 3)
	x[0] = 65
	x[1] = 66
	x[2] = 67
	return byteSliceToString(x) == "ABC"
}
