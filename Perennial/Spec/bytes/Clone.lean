/-
`bytes.Clone`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `bytes.Clone(b)`: a fresh, owned copy of `b`. -/
abbrev bytes.Clone.spec : Prop :=
  ∀ (sl_b : GoSlice) (dq : DFrac) (b : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗
       "Hsl_b" ∷ sl_b ↦*{dq} b }}
      (App (Val (@! Clone)) (Val #sl_b))
    {{ (sl_b' : GoSlice), RET #sl_b';
       "Hsl_b" ∷ sl_b ↦*{dq} b ∗
       "Hsl_b'" ∷ sl_b' ↦* b ∗
       "Hsl_b'_cap" ∷ ownSliceCap w8 sl_b' (DFrac.own 1) }}

end spec

end Perennial
