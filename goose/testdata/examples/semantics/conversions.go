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

const negUnderflow32Const = -1e-50

const bigIntegralFloatConst = 1e18 + 1

type myFloat32 float32

type myInt64 int64

func offTieAt[T ~float32]() T {
	return offTieConst
}

func offTieConvertedAt[T ~float32]() T {
	return T(offTieConst)
}

func negUnderflowAt[T ~float32]() T {
	return negUnderflow32Const
}

func bigIntegralAt[T ~int64]() T {
	return bigIntegralFloatConst
}

// an untyped float constant at a type parameter is rounded once, from its
// exact value, at the instantiation; -1e-50 rounds to +0
func testUntypedFloatConstAtTypeParam() bool {
	return offTieAt[float32]() == 1+0x1p-23 && offTieAt[myFloat32]() == 1+0x1p-23 &&
		1/negUnderflowAt[float32]() > 0 && 1/negUnderflowAt[myFloat32]() > 0
}

// T(c) at a type parameter converts c's default type, float64, so it rounds
// c to float64 (the tie 1+0x1p-24) and then to float32 (1, the even one)
func testUntypedFloatConvertAtTypeParam() bool {
	return offTieConvertedAt[float32]() == 1 && offTieConvertedAt[myFloat32]() == 1
}

// an integral untyped float constant converts to an integer type exactly (its
// float64 rounding would be 1e18)
func testUntypedFloatConstToInt() bool {
	var x int64 = bigIntegralFloatConst
	y := int64(bigIntegralFloatConst)
	var z uint64 = 1e19
	const w = -bigIntegralFloatConst
	var v int64 = w
	return x == 1000000000000000001 && y == x && z == 10000000000000000000 && v == -x &&
		bigIntegralAt[int64]() == x && bigIntegralAt[myInt64]() == 1000000000000000001
}

const posZeroF64 float64 = 0

const tinyF64 float64 = 1e-320

// a typed float64 constant expression is a constant: -0 and an underflow of a
// negative constant product are +0
func testFloat64ConstExprIsConst() bool {
	x := -posZeroF64
	y := -tinyF64 * 1e-10
	return 1/x > 0 && 1/y > 0
}
