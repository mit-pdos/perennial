/-
`math/big.(*Int).Int64`'s spec.
-/
module

public import Perennial.Proof.math.big.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

/-- `(*Int).Int64` of a `big.Int` holding `z` in the `int64` range: `z`. -/
abbrev math.big.Int.Int64.spec : Prop :=
  ∀ (p : Loc) (z : _root_.Int), - 2 ^ 63 ≤ z ∧ z < 2 ^ 63 →
    {{ math.big.ownInt (GF := GF) p z }}
      (App (Val (p @!! go.GoType.PointerType math.big.Int'.ty @!! go!"Int64")) (Val #()))
    {{ RET #(W64 z); math.big.ownInt p z }}

end spec

end Perennial
