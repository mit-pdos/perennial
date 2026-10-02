package unittest

func variadicFunc(a uint64, b string, cs ...byte) {
}

func testVariadicCall() {
	variadicFunc(10, "abc", 0, 1, 2, 3)
	variadicFunc(10, "abc")
	var c []byte
	variadicFunc(10, "abc", c...)
}

func returnMultiple() (uint64, string, uint8, uint8) {
	return 0, "xyz", 0, 0
}

func testVariadicPassThrough() {
	variadicFunc(returnMultiple())
}
