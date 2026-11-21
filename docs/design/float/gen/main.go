// Command gen prints test vectors of Go's float64 and float32 operations, computed by the Go
// toolchain running it, for the differential test of the Lean IEEE 754 definitions
// (Perennial/Golang/Defn/Float.lean) by ../check.lean. See ../README.md.
//
// Each line is `op a [b] result`, operands and result in hexadecimal bits (`true`/`false`
// for comparisons). Usage: go run ./docs/design/float/gen [-n N] [-seed S] > vectors.txt
package main

import (
	"bufio"
	"flag"
	"fmt"
	"math"
	"math/rand"
	"os"
)

var w *bufio.Writer

// Edge cases of float64: zeros, subnormals, min/max normal, infinities, NaNs (quiet, signaling,
// negative, with payload), small integers, values around 1 and 2^53.
var edges64 = []uint64{
	0, 1 << 63, // ±0
	1, 2, 3, 0x000FFFFFFFFFFFFF, 0x0008000000000000, // subnormals
	0x0010000000000000, 0x0010000000000001, 0x7FEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFE, // min/max normal
	0x7FF0000000000000,                                                                                 // +Inf
	0x7FF8000000000000, 0x7FF8000000000001, 0x7FF0000000000001, 0xFFF8000000000000, 0x7FFFFFFFFFFFFFFF, // NaNs
	0x3FF0000000000000, 0x3FF0000000000001, 0x3FEFFFFFFFFFFFFF, 0x3FE0000000000000, // 1, 1+ulp, 1-ulp/2, 0.5
	0x4000000000000000, 0x4008000000000000, 0x4340000000000000, 0x4340000000000001, // 2, 3, 2^53, 2^53+2
	0x3CA0000000000000, 0x3CB0000000000000, // 2^-53, 2^-52
	0x3FB999999999999A,                                                             // 0.1
	0x41CDCD6500000000,                                                             // 1e9
	0x47EFFFFFE0000000, 0x47EFFFFFF0000000, 0x36A0000000000000, 0x3690000000000000, // float32 max, its halfway, float32 min subnormal, its half
}

var edges32 = []uint32{
	0, 1 << 31, 1, 2, 0x007FFFFF, 0x00400000, 0x00800000, 0x00800001, 0x7F7FFFFF, 0x7F7FFFFE,
	0x7F800000, 0x7FC00000, 0x7FC00001, 0x7F800001, 0xFFC00000, 0x7FFFFFFF,
	0x3F800000, 0x3F800001, 0x3F7FFFFF, 0x3F000000, 0x40000000, 0x40400000, 0x4B800000, 0x33800000,
	0x3DCCCCCD,
}

func withSigns64(xs []uint64) []uint64 {
	var r []uint64
	for _, x := range xs {
		r = append(r, x, x^(1<<63))
	}
	return r
}

func withSigns32(xs []uint32) []uint32 {
	var r []uint32
	for _, x := range xs {
		r = append(r, x, x^(1<<31))
	}
	return r
}

// A random float64: uniform bits, or a sparse significand (few bits set, so sums and products
// often land exactly halfway between two floats), or near a given exponent.
func rand64(r *rand.Rand) uint64 {
	switch r.Intn(4) {
	case 0:
		return r.Uint64()
	case 1:
		e := uint64(r.Intn(2048))
		m := uint64(0)
		for i := r.Intn(4); i > 0; i-- {
			m |= 1 << r.Intn(52)
		}
		return uint64(r.Intn(2))<<63 | e<<52 | m
	case 2: // moderate exponents, where most arithmetic is finite
		e := uint64(1023 - 60 + r.Intn(120))
		return uint64(r.Intn(2))<<63 | e<<52 | r.Uint64()&(1<<52-1)
	default: // tiny: subnormal results
		e := uint64(r.Intn(60))
		return uint64(r.Intn(2))<<63 | e<<52 | r.Uint64()&(1<<52-1)
	}
}

// A second operand related to x: same or nearby exponent (cancellation, ties), or random.
func related64(r *rand.Rand, x uint64) uint64 {
	switch r.Intn(3) {
	case 0:
		return rand64(r)
	case 1:
		e := int((x >> 52) & 0x7FF)
		e += r.Intn(120) - 60
		if e < 0 {
			e = 0
		}
		if e > 2046 {
			e = 2046
		}
		m := x & (1<<52 - 1)
		if r.Intn(2) == 0 {
			m = 1 << r.Intn(52)
		}
		return uint64(r.Intn(2))<<63 | uint64(e)<<52 | m
	default:
		return x ^ uint64(r.Intn(4))<<62 ^ uint64(r.Intn(8)) // ±x, ±2x-ish, nearby
	}
}

func rand32(r *rand.Rand) uint32 {
	switch r.Intn(3) {
	case 0:
		return r.Uint32()
	case 1:
		e := uint32(r.Intn(256))
		m := uint32(0)
		for i := r.Intn(4); i > 0; i-- {
			m |= 1 << r.Intn(23)
		}
		return uint32(r.Intn(2))<<31 | e<<23 | m
	default:
		e := uint32(127 - 30 + r.Intn(60))
		return uint32(r.Intn(2))<<31 | e<<23 | r.Uint32()&(1<<23-1)
	}
}

func related32(r *rand.Rand, x uint32) uint32 {
	if r.Intn(2) == 0 {
		return rand32(r)
	}
	return x ^ uint32(r.Intn(4))<<30 ^ uint32(r.Intn(8))
}

func b64(x uint64) float64 { return math.Float64frombits(x) }
func b32(x uint32) float32 { return math.Float32frombits(x) }

func bin64(a, b uint64) {
	x, y := b64(a), b64(b)
	fmt.Fprintf(w, "add64 %x %x %x\n", a, b, math.Float64bits(x+y))
	fmt.Fprintf(w, "sub64 %x %x %x\n", a, b, math.Float64bits(x-y))
	fmt.Fprintf(w, "mul64 %x %x %x\n", a, b, math.Float64bits(x*y))
	fmt.Fprintf(w, "div64 %x %x %x\n", a, b, math.Float64bits(x/y))
	fmt.Fprintf(w, "leb64 %x %x %t\n", a, b, x <= y)
	fmt.Fprintf(w, "eq64 %x %x %t\n", a, b, x == y)
	fmt.Fprintf(w, "lt64 %x %x %t\n", a, b, x < y)
}

func un64(a uint64) {
	x := b64(a)
	fmt.Fprintf(w, "neg64 %x %x\n", a, math.Float64bits(-x))
	fmt.Fprintf(w, "f64to32 %x %x\n", a, math.Float32bits(float32(x)))
}

func bin32(a, b uint32) {
	x, y := b32(a), b32(b)
	fmt.Fprintf(w, "add32 %x %x %x\n", a, b, math.Float32bits(x+y))
	fmt.Fprintf(w, "sub32 %x %x %x\n", a, b, math.Float32bits(x-y))
	fmt.Fprintf(w, "mul32 %x %x %x\n", a, b, math.Float32bits(x*y))
	fmt.Fprintf(w, "div32 %x %x %x\n", a, b, math.Float32bits(x/y))
	fmt.Fprintf(w, "leb32 %x %x %t\n", a, b, x <= y)
	fmt.Fprintf(w, "eq32 %x %x %t\n", a, b, x == y)
	fmt.Fprintf(w, "neg32 %x %x\n", a, math.Float32bits(-x))
}

func ints(n uint64) {
	fmt.Fprintf(w, "i64to64 %x %x\n", n, math.Float64bits(float64(int64(n))))
	fmt.Fprintf(w, "u64to64 %x %x\n", n, math.Float64bits(float64(n)))
	m := uint32(n)
	fmt.Fprintf(w, "i32to64 %x %x\n", m, math.Float64bits(float64(int32(m))))
	fmt.Fprintf(w, "u32to64 %x %x\n", m, math.Float64bits(float64(m)))
}

// An integer near a power of two, with a random low part: exercises the rounding of
// conversions to float64 (ties at 2^54+2, ...).
func randInt(r *rand.Rand) uint64 {
	switch r.Intn(3) {
	case 0:
		return r.Uint64()
	case 1:
		k := r.Intn(64)
		return 1<<k + uint64(r.Intn(8)) - 4
	default:
		k := 53 + r.Intn(11)
		return (r.Uint64() >> (64 - k)) | 1<<(k-1) // k-bit integers, which need rounding
	}
}

func main() {
	n := flag.Int("n", 100000, "random cases per operation group")
	seed := flag.Int64("seed", 1, "random seed")
	flag.Parse()
	w = bufio.NewWriter(os.Stdout)
	defer w.Flush()
	r := rand.New(rand.NewSource(*seed))

	e64, e32 := withSigns64(edges64), withSigns32(edges32)
	for _, a := range e64 {
		un64(a)
		for _, b := range e64 {
			bin64(a, b)
		}
	}
	for _, a := range e32 {
		for _, b := range e32 {
			bin32(a, b)
		}
	}
	for _, x := range []uint64{0, 1, 1<<63 - 1, 1 << 63, 1<<64 - 1, 1 << 53, 1<<53 + 1, 1<<54 + 2, 1<<54 + 6,
		1<<63 - 512, 1<<63 - 513, 1<<64 - 1024, 1<<64 - 1025, 1 << 31, 1<<31 - 1, 1<<32 - 1, 1<<24 + 1} {
		ints(x)
		ints(-x)
	}
	for i := 0; i < *n; i++ {
		a := rand64(r)
		bin64(a, related64(r, a))
		un64(rand64(r))
		c := rand32(r)
		bin32(c, related32(r, c))
		ints(randInt(r))
	}
}
