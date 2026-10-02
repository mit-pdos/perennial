package semantics

func FirstClassFunction(a uint64) uint64 {
	return a + 10
}

func ApplyF(a uint64, f func(uint64) uint64) uint64 {
	return f(a)
}

func testFirstClassFunction() bool {
	return ApplyF(1, FirstClassFunction) == 11
}
