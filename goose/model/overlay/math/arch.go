// The Go models of package math's amd64 assembly (Perennial/Code/math.toml,
// [model]), spliced into floor_asm.go, exp_asm.go and log_asm.go in place of
// the bodyless declarations; the assembly files are blanked (blank_asm). The
// rest of the package is the real Go, translated. Differential test:
// goose/model/difftests/math_test.go (etc/model-tests.sh).

package math

import "internal/gomodel"

// MODEL: archFloor (floor_amd64.s) is Floor on amd64; gc also compiles a
// direct call of Floor to ROUNDSD under SSE4.1 (makeRoundAMD64,
// cmd/compile/internal/ssagen/intrinsics.go). On a non-NaN input both return
// the exact IEEE floor, which Go's portable floor (floor.go) computes: the
// model returns it. On a NaN they return a NaN, but not always the input's
// bits (ROUNDSD quiets a signaling NaN, the assembly returns it unchanged), so
// the model returns some NaN (chooseNaN). Measured on 2.2 million inputs
// (random bit patterns, NaN payloads, ±Inf, ±0, subnormals, values near 2^52):
// no other difference.
func archFloor(x float64) float64 {
	if x != x {
		return chooseNaN()
	}
	return floor(x)
}

// MODEL: archCeil (floor_amd64.s) is Ceil on amd64 (and ROUNDSD, as for
// archFloor): on a non-NaN input the exact IEEE ceiling, Go's portable ceil
// (floor.go); on a NaN some NaN.
func archCeil(x float64) float64 {
	if x != x {
		return chooseNaN()
	}
	return ceil(x)
}

// MODEL: archTrunc (floor_amd64.s) is Trunc on amd64 (and ROUNDSD, as for
// archFloor): on a non-NaN input the exact IEEE truncation, Go's portable
// trunc (floor.go); on a NaN some NaN.
func archTrunc(x float64) float64 {
	if x != x {
		return chooseNaN()
	}
	return trunc(x)
}

// MODEL: archExp (exp_amd64.s) is Exp on amd64, an algorithm of its own (with
// an FMA variant chosen by useFMA) whose results may differ in the last bit
// from Go's portable exp; it returns a float64 and cannot panic (register
// arithmetic, local jumps, no call). The model returns some float64.
func archExp(x float64) float64 {
	return Float64frombits(gomodel.ChooseUint64())
}

// MODEL: archLog (log_amd64.s) is Log on amd64, as archExp for exp: the model
// returns some float64.
func archLog(x float64) float64 {
	return Float64frombits(gomodel.ChooseUint64())
}

// chooseNaN is some NaN: the exponent all ones and a nonzero fraction, any
// sign and payload (in Go, 0x7FF0000000000001).
func chooseNaN() float64 {
	b := gomodel.ChooseUint64() | 0x7FF0000000000000
	if b&(1<<52-1) == 0 {
		b |= 1
	}
	return Float64frombits(b)
}
