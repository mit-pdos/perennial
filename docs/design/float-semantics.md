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
and unbounded range, then rounded), with no dependency beyond Lean core (`Rat`, `BitVec`).
The structure: **decode the operands, compute and round in the decoded (exact) space, then
encode the result**, where encoding is a relation that handles NaN.

- `Format`: a binary interchange format given by its exponent width `w` and trailing
  significand width `t` (so `p = t + 1`, `emax = 2^(w-1) - 1`, `emin = 1 - emax`);
  `binary64 = ⟨11, 52⟩`, `binary32 = ⟨8, 23⟩`.
- `Datum := nan | inf (neg : Bool) | finite (neg : Bool) (m : Rat)`: a floating-point datum,
  with a finite number as a sign and an exact magnitude (`finite s 0` is `±0`).
- `decode : Bits → Datum` (`±0`, subnormals `0.T × 2^emin`, normals `1.T × 2^(E - bias)`,
  `±∞`, NaN).
- `round : Bool → Rat → Datum`: round to nearest, ties to even, on the subnormal grid below
  `2^emin`; overflow to `±∞`; a result that rounds to zero keeps its sign. The only
  algorithmic part.
- `add sub mul div : Bits → Bits → Datum`, `neg : Bits → Datum`: the standard's special cases
  (NaN propagation; the invalid operations `∞ - ∞`, `0 × ∞`, `0 / 0`, `∞ / ∞`; `x / 0 = ±∞`;
  signed zeros: an exact zero sum is `+0` except `(-0) + (-0) = -0`, so `x - x = +0`; the sign
  of a product or quotient is the exclusive or), otherwise the rounding of the exact rational
  result. `x - y` is `x + (-y)`; neg flips the sign. `ofInt : Int → Datum` rounds;
  `convert g : Bits → Datum` rounds at format `g` (NaN stays NaN).
- `leb eq : Bits → Bits → Bool` compare decoded values (NaN unordered, `-0 == +0`).
- `encode : Datum → Option Bits`: the unique bit pattern of a non-NaN datum (`none` for NaN);
  `encodes : Datum → Bits → Prop`: `b` is that pattern, or any NaN for NaN.

No NaN bit pattern appears in the operations. The definitions are computable (tested with
`lean --run`) and written to be read, not to be fast. The operations are sealed
(`@[irreducible]` with `_unseal` lemmas), so automation does not unfold rounding in unrelated
proofs.

## NaN nondeterminism (`float64Encodes`, `float32Encodes`)

The sign and payload of a NaN result are architecture-dependent: amd64's default NaN has the
sign bit set, arm64's does not, and a constant-folded operation may differ from the same
operation at run time. So the model says only that the result is *a* NaN. Mechanism: the
arithmetic step rules are relations on `is_go_step_pure`, like `go_prealloc_step`, that encode
the operation's datum:

```lean
plus_float64 {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
  is_go_step_pure (GoOp GoPlus t) glv((#v1, #v2)) =
    fun (e : Expr) => ∃ f, e = #f ∧ float64Encodes (float64Add v1 v2) f
```

So `x + y` steps to the bit pattern of IEEE 754's result, or to any NaN if it is NaN. The
rules are stated at every type `t` whose underlying type is `float64` (`float32`), because
`go_op_underlying`/`go_un_op_underlying` lift only deterministic (`⤳[under]`) rules to named
types; `CoreSemantics` is unchanged. Being equations rather than instances, they are used
through the wp lemmas below. Alternatives considered:

- keep `FloatOps` as a class whose fields agree with IEEE 754 up to NaN: NaN bits would be a
  deterministic function of the operands, which is stronger than Go promises (constant
  folding, cross-compilation) and keeps an extra class in the trusted base;
- operations returning bits with a placeholder NaN, which the step rule replaced by any NaN
  (an earlier version of this design, first with GooseLang code choosing the NaN): the
  placeholder was meaningless; returning the datum avoids it.

`FloatOps` is therefore removed: its fields are now plain definitions with the same names
(`float64Add`, ...; the arithmetic ones now return a `Datum`), and nothing instantiates them.

Which operations are nondeterministic: `+ - * /` and unary `-` (also of a NaN: IEEE 754 and gc
on amd64 flip the sign bit of a NaN, but the Go spec does not promise it, and not every target
has a non-arithmetic negation). Comparisons (`==`, `<`, ...) and integer-to-float conversions
never produce a NaN and stay deterministic `⤳[under]` rules, so automation steps them; the
conversions return bits, `(encode (ofInt n)).getD 0` (a rounding is never NaN, so the default
is never used). `float32(c)` of an untyped constant is deterministic too, `float64ToFloat32`
(a constant is never NaN). There is no rule for `float32(x)` of a `float64` variable.
Float-to-integer conversion is unchanged (`ArbitraryInt`, implementation-defined in Go).

In proofs, each arithmetic operation takes one `wp_apply`: `wp_apply wp_float64_add as %f Hf`
(likewise `_sub`, `_mul`, `_div`, `_neg` and the `float32` ones), with
`Hf : float64Encodes (float64Add v1 v2) f` (see `Proof/time/Duration__Seconds.lean`). They are
instances of `wp_go_step_rel`, the spec of any instruction with a relational pure step.

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
integer has a clear sign bit), from `Format.round_cases` (a rounding has the sign it is given).

## Testing

`docs/design/float/README.md`: Go prints vectors (edge cases and random bit patterns biased to
rounding ties, cancellation, overflow and underflow), and `check.lean` checks the Lean
definitions against them: Go's bits must encode the datum Lean computes (`encodes`), so Lean
predicts a NaN exactly when Go produces one, and the exact bits otherwise.
