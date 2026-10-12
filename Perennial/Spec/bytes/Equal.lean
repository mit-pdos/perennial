/-
`bytes.Equal`'s spec.
-/
module

public import Perennial.Proof.bytes.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `bytes.Equal(b0, b1)`: whether `b0` and `b1` hold the same bytes. -/
abbrev bytes.Equal.spec : Prop :=
  ∀ (sl_b0 sl_b1 : GoSlice) (d0 d1 : DFrac) (b0 b1 : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗
       "Hb0" ∷ sl_b0 ↦*{d0} b0 ∗
       "Hb1" ∷ sl_b1 ↦*{d1} b1 }}
      (App (App (Val (@! Equal)) (Val #sl_b0)) (Val #sl_b1))
    {{ RET #(decide (b0 = b1));
       sl_b0 ↦*{d0} b0 ∗
       sl_b1 ↦*{d1} b1 }}

end spec

end Perennial
