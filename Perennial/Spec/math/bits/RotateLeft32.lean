/-
`math.bits.RotateLeft32`'s spec.
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

/-- `RotateLeft32(x, k)` is `x` rotated left by `k mod 32` bits (`k` as a `uint`, so a negative
`k` rotates right). -/
abbrev math.bits.RotateLeft32.spec : Prop :=
  ∀ (x : w32) (k : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (App (Val (@! RotateLeft32)) (Val #x)) (Val #k))
    {{ RET #(x.rotateLeft (k.toNat % 32)); True }}

end spec

end Perennial
