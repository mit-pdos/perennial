# Float evidence and differential test

- `float_test.go` (`go test ./docs/design/float`): Go facts behind the float rules (negation
  flips the sign bit of every value, float-to-integer conversions do not panic, the sign
  facts of `Perennial/Golang/Theory/Float.lean`).
- `gen/` and `check.lean`: the differential test of the IEEE 754 definitions
  (`Perennial/Golang/Defn/Float.lean`) against Go. `gen` prints vectors computed by Go, one
  per line (`op a [b] result`, bits in hex): all pairs of float64/float32 edge cases (±0,
  subnormals, min/max normal, ±∞, quiet/signaling/negative NaNs, 1 ± ulp, 2^53, rounding
  halfway points of float32), special integers, and `-n` random cases per group (uniform bits;
  sparse significands, which make exact ties; nearby exponents, for cancellation; tiny values,
  for subnormal results; integers of 53–64 bits for conversions). `check.lean` evaluates the
  Lean definitions on them; two NaN results agree whatever their bits, since the semantics
  allows any NaN.

Operations: float64 and float32 `+ - * / <= ==` and unary `-`, float64 `<` (as the semantics
encodes it, `Leb && !Eq`), `float32(x)` of a float64, and `float64(n)` of int64, uint64, int32
and uint32.

Run (from the repository root, after `lake build Perennial.Golang.Defn.Float`):

```sh
go run ./docs/design/float/gen -n 250000 -seed 7 > /tmp/vectors.txt
lake env lean --run docs/design/float/check.lean /tmp/vectors.txt
```

`check.lean` prints the count per operation and `N vectors, 0 mismatches`, and exits non-zero
on a mismatch (printing the first 20). It checks about 30,000 vectors per second (interpreted).

Results (go1.27.3 linux/amd64): seed 7, `-n 250000`: 5,048,260 vectors, 0 mismatches; seed 8,
`-n 1000000`: 20,048,260 vectors, 0 mismatches.
