# Float semantics

How the Go semantics models `float64` and `float32`: concrete IEEE 754 arithmetic, with an
arbitrary NaN wherever IEEE 754's result is a NaN. Definitions:
`Perennial/Golang/Defn/Float.lean` (the arithmetic) and the float classes of
`Perennial/Golang/Defn/Predeclared.lean` (the step rules); lemmas:
`Perennial/Golang/Theory/Float.lean`; differential test against Go: `docs/design/float/`.

Guiding principle: the semantics is as conservative and underspecified as possible while still
letting us reason about the code we need.

## Representation

A float is its bit pattern, a `w64` or `w32` (option 8b of
`unsafe-memory-prerequisites.md`, a separate float value, was rejected). Before this design
the operations were the uninterpreted fields of a class `FloatOps` (a field of
`GoSemanticsFunctions`), so no fact about a float result was provable; proofs that needed one
(`float64(n) >= 0` for prometheus' `counter.Add`) had to add axioms.

## The arithmetic (`Defn/Float.lean`)

Written in the standard's own terms (IEEE 754-2019 §4.3: computed as if to infinite precision
and unbounded range, then rounded), with no dependency beyond Lean core (`Rat`, `BitVec`):

- `Format`: a binary interchange format given by its exponent width `w` and trailing
  significand width `t` (so `p = t + 1`, `emax = 2^(w-1) - 1`, `emin = 1 - emax`);
  `binary64 = ⟨11, 52⟩`, `binary32 = ⟨8, 23⟩`.
- `decode : Bits → Datum`: NaN, `±∞`, or a finite number as sign and exact rational
  magnitude (`±0`, subnormals `0.T × 2^emin`, normals `1.T × 2^(E - bias)`).
- `round s m`: round to nearest, ties to even, on the subnormal grid below `2^emin`, overflow
  to `±∞`; a result that rounds to zero keeps the sign `s`. This is the only algorithmic part.
- add/sub/mul/div: the standard's special cases (NaN propagation; the invalid operations
  `∞ - ∞`, `0 × ∞`, `0 / 0`, `∞ / ∞`; `x / 0 = ±∞`; signed zeros: an exact zero sum is `+0`
  except `(-0) + (-0) = -0`, so `x - x = +0`; the sign of a product or quotient is the
  exclusive or), otherwise the rounding of the exact rational result. `x - y` is `x + (-y)`.
- neg flips the sign bit; comparisons compare exact values (NaN unordered, `-0 == +0`);
  integer to float is the rounding of the integer; `float64` to `float32` rounds the value at
  binary32.

The definitions are computable (tested with `#eval`/`lean --run`) and written to be read, not
to be fast. The operations are sealed (`@[irreducible]` with `_unseal` lemmas), so automation
does not unfold rounding in unrelated proofs.

## NaN nondeterminism (`go.float64Result`, `go.float32Result`)

The sign and payload of a NaN result are architecture-dependent: amd64's default NaN has the
sign bit set, arm64's does not, and a constant-folded operation may differ from the same
operation at run time. So the model says only that the result is *a* NaN. Mechanism: the step
rule of every arithmetic operation steps to `float64Result r`, where `r` is the IEEE 754
result computed above:

```lean
def float64ResultDef (r : w64) : Expr :=
  if float64IsNaN r then
    gl(let: "x" := ArbitraryInt in if: "x" =⟨go.float64⟩ "x" then #float64NaN else "x")
  else Val #r
```

That is, `r` itself when it is not a NaN, and otherwise an arbitrary NaN: an arbitrary bit
pattern (the existing `ArbitraryInt`, as for float-to-integer conversion), kept if it is a NaN
(`x != x`) and replaced by a fixed NaN if not, so that every NaN, and only NaNs, can result.
This needs no new primitive or Go instruction. (The fixed `Format.nan` that `Float.lean`
returns for a NaN result is never observed.) Alternatives considered:

- keep `FloatOps` as a class whose fields agree with IEEE 754 up to NaN: NaN bits would be a
  deterministic function of the operands, which is stronger than Go promises (constant
  folding, cross-compilation) and keeps an extra class in the trusted base;
- a new internal Go instruction producing a NaN: a language change for no gain.

`FloatOps` is therefore removed: its fields are now plain definitions with the same names
(`float64Add`, ...), and nothing instantiates them.

Which operations are nondeterministic: `+ - * /` and unary `-` (also of a NaN: IEEE 754 and gc
on amd64 flip the sign bit of a NaN, but the Go spec does not promise it, and not every target
has a non-arithmetic negation). Comparisons (`==`, `<`, ...) and integer-to-float conversions
never produce a NaN and stay deterministic, so automation steps them without a choice.
`float32(c)` of an untyped constant is deterministic too (a constant is never a NaN).
Float-to-integer conversion is unchanged (`ArbitraryInt`, implementation-defined in Go).

In proofs, `wp_apply wp_float64Result as %f %Hf` takes the step, with
`Hf : f = r ∨ (float64IsNaN r ∧ float64IsNaN f)` (see `Proof/time/Duration__Seconds.lean`).

## Known limitations

- **Fused multiply-add is not modelled.** The Go spec allows an implementation to fuse float
  operations, computing `x*y + z` with one rounding (gc emits `FMADDD` for it on arm64). The
  model rounds every operation, so it is *more* defined than Go here: a proof about such an
  expression is about the unfused evaluation only (`docs/KNOWN_LIMITATIONS.md`, "Floats").
- `float32(c)` of an untyped constant rounds the constant's `float64` rounding (goose's
  representation), not the constant: double rounding (`docs/KNOWN_LIMITATIONS.md`).
- Not modelled (stuck, hence sound): `float64` ↔ `float32` conversions of variables, integer to
  `float32` conversions, integer types narrower than 32 bits to floats.

## Lemmas (`Theory/Float.lean`)

The facts PR #648 had proposed as axioms are theorems: `lt_zero_false_of_sign_clear` (a
`float64` with a clear sign bit is not `< +0`, stated on `float64Leb x 0 && !float64Eq x 0`,
the form `lt_float64` steps to; `lt_float64_zero_step_of_sign_clear` is the step of `x < 0` to
`false`), and `{int64,uint64,int32,uint32}ToFloat64_sign_clear` (`float64(n)` of a non-negative
integer has a clear sign bit), from `Format.msb_round` (a rounding has the sign it is given).

## Testing

`docs/design/float/README.md`: Go prints vectors (edge cases and random bit patterns biased to
rounding ties, cancellation, overflow and underflow), and `check.lean` checks the Lean
definitions against them, any two NaNs agreeing.
