package unittest

const (
	a = 1.0
	b = 1e6
)

func useFloat() float64 {
	x := a
	x = (x + a) * 1.0
	return x
}

func compareIntFloat(x int) bool {
	return x < b
}

func compareFloatInt(x int) bool {
	return b < x
}

const (
	negUnderflow            = -1e-400
	negUnderflow32          = -1e-50
	negUnderflowF64 float64 = -1e-400
	negUnderflowF32 float32 = -1e-50
)

func negUnderflowConsts() (float64, float32, float64, float32, float64, float32) {
	const local = -1e-400
	const local32 float32 = -1e-50
	var x float32 = negUnderflow32
	return negUnderflow, x, negUnderflowF64, negUnderflowF32, local, local32
}

func negUnderflowLiterals() (float64, float32) {
	x := -1e-400
	var y float32 = -1e-50
	return x, y
}

const (
	offTie                = 1 + 0x1p-24 + 0x1p-60
	offTieF32     float32 = 1 + 0x1p-24 + 0x1p-60
	underflowF32  float32 = -1e-50
	offTieUntyped         = offTie
)

type float32Field struct {
	f float32
}

func takeFloat32(x float32) float32 {
	return x
}

func float32Consts() []float32 {
	const local float32 = 1 + 0x1p-24 + 0x1p-60
	var a float32 = offTie
	var b float32 = -1e-50
	c := float32(1 + 0x1p-24 + 0x1p-60)
	d := float32(offTie)
	a = 1 + 0x1p-24 + 0x1p-60
	b = negUnderflow32
	s := float32Field{f: offTie}
	t := float32Field{f: -1e-50}
	arr := [2]float32{offTie, -1e-50}
	e := a + (0x1p-24 + 0x1p-60)
	return []float32{a, b, c, d, local, offTieF32, underflowF32, s.f, t.f, arr[0], arr[1], e,
		takeFloat32(offTie), takeFloat32(-1e-50), takeFloat32(offTieUntyped)}
}

const bigIntegral = 1e18 + 1

func float32ConstAt[T ~float32]() (T, T, T) {
	return offTie, T(offTie), -offTie
}

func intConstAt[T ~int64]() (T, int64) {
	var x int64 = bigIntegral
	return bigIntegral, x
}
