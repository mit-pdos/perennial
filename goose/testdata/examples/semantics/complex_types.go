package semantics

// The complex cases of a type switch on a value of another type are skipped (as in
// fmt's printArg, whose complex cases come first).
func testTypeSwitchComplex() bool {
	var x any = float32(0)
	switch x.(type) {
	case complex64:
		return false
	case complex128:
		return false
	case float32:
		return true
	}
	return false
}

// A failed assertion to a complex type reports false.
func testAssertComplexFails() bool {
	var x any = float64(0)
	_, ok64 := x.(complex64)
	_, ok128 := x.(complex128)
	return !ok64 && !ok128
}

// The zero values of the complex types: an interface holding one asserts to its type only,
// and equals the zero value of its type, not that of the other complex type.
func testComplexZeroValue() bool {
	var x any = [1]complex64{}[0]
	var y any = [1]complex128{}[0]
	_, ok64 := x.(complex64)
	_, ok128 := x.(complex128)
	_, yok := y.(complex128)
	return ok64 && !ok128 && yok && x == any([1]complex64{}[0]) &&
		y == any([1]complex128{}[0]) && x != y
}
