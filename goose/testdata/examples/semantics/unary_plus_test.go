package semantics

import (
	"math"
	"testing"
)

// Go evidence for the semantics' `pos_*` rules (Golang/Defn/Predeclared.lean): `+x` is `x` bit for
// bit at the float types too, including -0, the infinities and every NaN payload.
func TestUnaryPlusFloatBits(t *testing.T) {
	for _, b := range []uint64{0, 1 << 63, 0x7ff0000000000000, 0xfff0000000000000,
		0x7ff8000000000001, 0xfff4000000000123, 0x3ff8000000000000, 1} {
		x := math.Float64frombits(b)
		if y := +x; math.Float64bits(y) != b {
			t.Fatalf("float64 %#x: +x has bits %#x", b, math.Float64bits(y))
		}
	}
	for _, b := range []uint32{0, 1 << 31, 0x7f800000, 0xff800000, 0x7fc00001, 0xffa00123, 1} {
		x := math.Float32frombits(b)
		if y := +x; math.Float32bits(y) != b {
			t.Fatalf("float32 %#x: +x has bits %#x", b, math.Float32bits(y))
		}
	}
}

// ... and the identity at every integer type, at the extremes.
func TestUnaryPlusIntExtremes(t *testing.T) {
	if x := int64(math.MinInt64); +x != x {
		t.Fatal("int64")
	}
	if x := int8(math.MinInt8); +x != x {
		t.Fatal("int8")
	}
	if x := uint64(math.MaxUint64); +x != x {
		t.Fatal("uint64")
	}
}
