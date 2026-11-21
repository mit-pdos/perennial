// Package float holds the Go evidence for the float rules and facts of the Go semantics
// (Perennial/Golang/Defn/Predeclared.lean, Float64Semantics and Float32Semantics): unary minus
// (neg_float64, neg_float32), float-to-integer conversions (convert_float64_to_integer), and the
// sign facts (lt_zero_false_of_sign_clear, *ToFloat64_sign_clear). Run: go test ./docs/design/float
package float

import (
	"math"
	"math/rand"
	"testing"
)

var sink int64

// neg_float64: -x runs on every float64 (no panic) and flips the sign bit, also of a zero, an
// infinity and a NaN; the model leaves it uninterpreted (float64Neg), which allows that.
func TestNeg(t *testing.T) {
	zero := 0.0 // a variable: -0.0 as a constant is +0
	cases := []float64{zero, math.Copysign(0, -1), 1.5, -2.25, math.Inf(1), math.Inf(-1), math.NaN(),
		math.SmallestNonzeroFloat64, math.MaxFloat64}
	for _, x := range cases {
		y := -x
		if math.Float64bits(y) != math.Float64bits(x)^(1<<63) {
			t.Errorf("-%v: bits %x, want %x", x, math.Float64bits(y), math.Float64bits(x)^(1<<63))
		}
	}
	if math.Float64bits(-zero) != 1<<63 {
		t.Errorf("-zero is not -0")
	}
	var f32 float32 = 3
	if -f32 != -3 {
		t.Errorf("float32 negation")
	}
}

// convert_float64_to_integer: int64(x) of a NaN, an infinity or an out-of-range float does
// not panic; its value is implementation-defined (Go spec, "Conversions between numeric
// types"), which the model's ArbitraryInt allows.
func TestFloatToIntNoPanic(t *testing.T) {
	for _, x := range []float64{math.NaN(), math.Inf(1), math.Inf(-1), 1e300, -1e300,
		math.Copysign(0, -1), 9.223372036854775807e18, -9.3e18} {
		sink += int64(x)
		sink += int64(uint64(x))
		sink += int64(int32(x))
		sink += int64(uint8(x))
	}
}

// lt_zero_false_of_sign_clear: a float64 with a clear sign bit (+0, positive, +Inf, a NaN) is
// not < +0.
func TestSignClearNotBelowZero(t *testing.T) {
	special := []uint64{0, 1, 0x7FF0000000000000, 0x7FF0000000000001, 0x7FF8000000000000,
		0x7FFFFFFFFFFFFFFF, 0x3FF0000000000000, 0x000FFFFFFFFFFFFF}
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 1000000; i++ {
		special = append(special, r.Uint64()&^(1<<63))
	}
	for _, b := range special {
		x := math.Float64frombits(b)
		if x < 0 {
			t.Fatalf("%x < 0", b)
		}
	}
	// the facts' premise matters: a set sign bit can be below +0 (-1), or not (-0, a NaN)
	if !(math.Float64frombits(0xBFF0000000000000) < 0) || math.Copysign(0, -1) < 0 || -math.NaN() < 0 {
		t.Fatalf("sign-set cases")
	}
}

// *ToFloat64_sign_clear: float64(n) of a non-negative integer has a clear sign bit (0 gives +0).
func TestIntToFloatSignClear(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	us := []uint64{0, 1, math.MaxUint64, 1 << 63, 1<<53 + 1}
	for i := 0; i < 1000000; i++ {
		us = append(us, r.Uint64())
	}
	for _, u := range us {
		if math.Float64bits(float64(u))>>63 != 0 {
			t.Fatalf("float64(uint64 %d)", u)
		}
		if n := int64(u &^ (1 << 63)); math.Float64bits(float64(n))>>63 != 0 {
			t.Fatalf("float64(int64 %d)", n)
		}
		if math.Float64bits(float64(uint32(u)))>>63 != 0 {
			t.Fatalf("float64(uint32 %d)", uint32(u))
		}
		if n := int32(uint32(u) &^ (1 << 31)); math.Float64bits(float64(n))>>63 != 0 {
			t.Fatalf("float64(int32 %d)", n)
		}
	}
	if math.Float64bits(float64(int64(math.MaxInt64))) != 0x43E0000000000000 {
		t.Fatalf("float64(MaxInt64) rounds up to 2^63")
	}
}
