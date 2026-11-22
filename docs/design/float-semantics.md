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
- `FloatValue := nan | inf (neg : Bool) | finite (neg : Bool) (m : Rat)`: the exact value of
  an operation's result: NaN, a signed infinity, or a sign and an exact rational magnitude
  (`finite s 0` is `±0`). Roughly IEEE 754's level-2 "floating-point data", except that
  `finite` may hold magnitudes the format cannot represent (only `decode` and `round`
  results are representable), which is why `encode` is meaningful only on those.
- `decode : Bits → FloatValue` (`±0`, subnormals `0.T × 2^emin`, normals `1.T × 2^(E - bias)`,
  `±∞`, NaN).
- `round : Bool → Rat → FloatValue`: round to nearest, ties to even, on the subnormal grid below
  `2^emin`; overflow to `±∞`; a result that rounds to zero keeps its sign. The only
  algorithmic part.
- `add sub mul div : Bits → Bits → FloatValue`, `neg : Bits → FloatValue`: the standard's
  special cases (NaN propagation; the invalid operations `∞ - ∞`, `0 × ∞`, `0 / 0`, `∞ / ∞`;
  `x / 0 = ±∞`; signed zeros: an exact zero sum is `+0` except `(-0) + (-0) = -0`, so `x - x = +0`; the sign
  of a product or quotient is the exclusive or), otherwise the rounding of the exact rational
  result. `x - y` is `x + (-y)`; neg flips the sign. `ofInt : Int → FloatValue` rounds;
  `convert g : Bits → FloatValue` rounds at format `g` (NaN stays NaN).
- `leb eq : Bits → Bits → Bool` compare decoded values (NaN unordered, `-0 == +0`).
- `encode : FloatValue → Option Bits`: the unique bit pattern of a representable non-NaN value
  (`none` for NaN); `encodes : FloatValue → Bits → Prop`: `b` is that pattern, or any NaN for
  NaN.

No NaN bit pattern appears in the operations. The definitions are computable (tested with
`lean --run`) and written to be read, not to be fast. The operations are sealed
(`@[irreducible]` with `_unseal` lemmas), so automation does not unfold rounding in unrelated
proofs.

## NaN nondeterminism (`float64Encodes`, `float32Encodes`)

The sign and payload of a NaN result are architecture-dependent: amd64's default NaN has the
sign bit set, arm64's does not, and a constant-folded operation may differ from the same
operation at run time. So the model says only that the result is *a* NaN. Mechanism: the
arithmetic step rules are relations on `is_go_step_pure`, like `go_prealloc_step`, that encode
the operation's value:

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
  placeholder was meaningless; returning the value avoids it.

`FloatOps` is therefore removed: its fields are now plain definitions with the same names
(`float64Add`, ...; the arithmetic ones now return a `FloatValue`), and nothing instantiates them.

Which operations are nondeterministic: `+ - * /` and unary `-` (also of a NaN: IEEE 754 and gc
on amd64 flip the sign bit of a NaN, but the Go spec does not promise it, and not every target
has a non-arithmetic negation). Comparisons (`==`, `<`, ...) and integer-to-float conversions
never produce a NaN and stay deterministic `⤳[under]` rules, so automation steps them; the
conversions return bits, `(encode (ofInt n)).getD 0` (a rounding is never NaN, so the default
is never used). A constant of type `float32` is emitted by goose as its `float32` value, rounded
once from the exact constant; there is no rule for converting an untyped float (the `float64`
rounding of a constant) to `float32`, which would round twice (reachable only in generic code,
`T(c)` with `T` a type parameter), nor for `float32(x)` of a `float64` variable.
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
- Not modelled (stuck, hence sound): `float64` ↔ `float32` conversions of variables, integer to
  `float32` conversions, integer types narrower than 32 bits to floats, untyped float constants
  to a type parameter instantiated with `float32` (goose cannot round them at the right type).

## Lemmas (`Theory/Float.lean`)

The facts PR #648 had proposed as axioms are theorems: `lt_zero_false_of_sign_clear` (a
`float64` with a clear sign bit is not `< +0`, stated on `float64Leb x 0 && !float64Eq x 0`,
the form `lt_float64` steps to; `lt_float64_zero_step_of_sign_clear` is the step of `x < 0` to
`false`), and `{int64,uint64,int32,uint32}ToFloat64_sign_clear` (`float64(n)` of a non-negative
integer has a clear sign bit), from `Format.round_cases` (a rounding has the sign it is given).

## Testing

`docs/design/float/README.md`: Go prints vectors (edge cases and random bit patterns biased to
rounding ties, cancellation, overflow and underflow), and `check.lean` checks the Lean
definitions against them: Go's bits must encode the value Lean computes (`encodes`), so Lean
predicts a NaN exactly when Go produces one, and the exact bits otherwise.
