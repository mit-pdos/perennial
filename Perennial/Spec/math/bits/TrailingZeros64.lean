/-
`math.bits.TrailingZeros64`'s spec.
-/
module

public import Perennial.Proof.math.bits.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- `TrailingZeros64(x)` returns: `64` for `x = 0`, and `k` for a power of two `x = 2 ^ k`. (The number
of trailing zero bits of any other `x` is not stated.) -/
abbrev math.bits.TrailingZeros64.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! TrailingZeros64)) (Val #x))
    {{ (r : w64), RET #r; ⌜(x = 0 → r = W64 64) ∧ ∀ k : Nat, k < 64 → x = W64 (2 ^ k) → r = W64 k⌝ }}

end spec

end Perennial
