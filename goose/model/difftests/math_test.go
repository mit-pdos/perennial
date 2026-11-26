//go:build difftests

// Differential tests of the Go models of package math's amd64 assembly
// (goose/model/overlay/math): built WITHOUT the overlay, they compare the
// real assembly (math.archFloor, archCeil, archTrunc, reached by linkname) and
// gc's code for math.Floor, Ceil and Trunc (the ROUNDSD instruction under
// SSE4.1, makeRoundAMD64 in cmd/compile/internal/ssagen/intrinsics.go) with
// the models' bodies: Go's portable floor, ceil and trunc (floor.go, also by
// linkname) on non-NaN inputs, and some NaN on NaN inputs. Run by
// etc/model-tests.sh with -tags difftests -ldflags=-checklinkname=0 (math's
// internal symbols are not linkname-pushed; the tag keeps go test ./... from
// linking it without the flag).
package difftests

import (
	"math"
	"math/rand"
	"testing"
	_ "unsafe"
)

//go:linkname archFloor math.archFloor
func archFloor(x float64) float64

//go:linkname archCeil math.archCeil
func archCeil(x float64) float64

//go:linkname archTrunc math.archTrunc
func archTrunc(x float64) float64

//go:linkname floor math.floor
func floor(x float64) float64

//go:linkname ceil math.ceil
func ceil(x float64) float64

//go:linkname trunc math.trunc
func trunc(x float64) float64

// model is a model's result: its portable body on a non-NaN input; on a NaN
// input any NaN (ok reports whether got is one of the model's results).
func ok(model func(float64) float64, x, got float64) bool {
	if math.IsNaN(x) {
		return math.IsNaN(got)
	}
	return math.Float64bits(got) == math.Float64bits(model(x))
}

func inputs() []float64 {
	var xs []float64
	bits := []uint64{
		0x7FF8000000000001, 0x7FF8000000000000, 0xFFF8000000000000, 0x7FF0000000000001,
		0xFFF0000000000001, 0x7FF4000000000000, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, // NaNs
		0x7FF0000000000000, 0xFFF0000000000000, // ±Inf
		0, 1 << 63, // ±0
		1, 0x000FFFFFFFFFFFFF, 0x8000000000000001, 0x800FFFFFFFFFFFFF, // subnormals
		0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, // smallest normal, ±max
	}
	for _, b := range bits {
		xs = append(xs, math.Float64frombits(b))
	}
	for _, v := range []float64{0.5, -0.5, 0.49999999999999994, 1, -1, 1.5, -1.5, 2.5, -2.5,
		1<<52 - 0.5, -(1<<52 - 0.5), 1 << 52, -(1 << 52), 1<<52 + 1, 1<<53 - 1, 1 << 63, -(1 << 63),
		1<<63 - 1024, 1e300, -1e300, 1e-300, -1e-300} {
		xs = append(xs, v, math.Nextafter(v, math.Inf(1)), math.Nextafter(v, math.Inf(-1)))
	}
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 2000000; i++ {
		xs = append(xs, math.Float64frombits(r.Uint64()))
	}
	// values of every magnitude around 2^52, and small ones with a fraction
	for i := 0; i < 200000; i++ {
		e := r.Intn(70) - 10
		v := math.Ldexp(1+r.Float64(), e)
		if r.Intn(2) == 0 {
			v = -v
		}
		xs = append(xs, v)
	}
	return xs
}

func TestRoundingModels(t *testing.T) {
	type c struct {
		name  string
		real  func(float64) float64
		model func(float64) float64
	}
	cases := []c{
		{"archFloor", archFloor, floor}, {"archCeil", archCeil, ceil}, {"archTrunc", archTrunc, trunc},
		// direct calls, which gc compiles to ROUNDSD (a func value math.Floor would call the assembly)
		{"Floor", func(x float64) float64 { return math.Floor(x) }, floor},
		{"Ceil", func(x float64) float64 { return math.Ceil(x) }, ceil},
		{"Trunc", func(x float64) float64 { return math.Trunc(x) }, trunc},
	}
	xs := inputs()
	nanBitsDiffer := map[string]int{}
	for _, k := range cases {
		bad := 0
		for _, x := range xs {
			got := k.real(x)
			if !ok(k.model, x, got) {
				if bad < 5 {
					t.Errorf("%s(%#016x) = %#016x, model %#016x", k.name, math.Float64bits(x),
						math.Float64bits(got), math.Float64bits(k.model(x)))
				}
				bad++
			}
			if math.IsNaN(x) && math.Float64bits(got) != math.Float64bits(k.model(x)) {
				nanBitsDiffer[k.name]++
			}
		}
		t.Logf("%s: %d inputs, %d mismatches, %d NaN inputs whose bits differ from the portable body's",
			k.name, len(xs), bad, nanBitsDiffer[k.name])
	}
}
