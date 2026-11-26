package semantics

// `x++` and `x--` at a float type add and subtract 1 (the Go spec: `x++` is `x += 1`, the untyped
// constant 1 converted to the type of x), at float64, float32 and a named float type.

type namedFloat64 float64

func testFloatIncDec() bool {
	f := 1.5
	f++
	var g float32 = -2.25
	g--
	var h namedFloat64 = 0.5
	h++
	h--
	h++
	return f == 2.5 && g == -3.25 && h == 1.5
}
