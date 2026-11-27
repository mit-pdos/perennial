/-
`math.bits.Mul`'s spec.
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

/-- `Mul(x, y)` (`uint` is 64 bits wide) is the full product of `x` and `y`, as its high and
low halves: `(hi, lo)` with `hi * 2^64 + lo = x * y`. -/
abbrev math.bits.Mul.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (App (Val (@! Mul)) (Val #x)) (Val #y))
    {{ RET (PairV #(W64 (uint.Z x * uint.Z y / 2 ^ 64)) #(x * y)); True }}

end spec

end Perennial
