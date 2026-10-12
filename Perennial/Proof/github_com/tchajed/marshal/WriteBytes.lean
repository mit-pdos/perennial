/-
The proof of `github.com/tchajed/marshal.WriteBytes`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.WriteBytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.WriteBytes.wp_proof :
    github_com.tchajed.marshal.WriteBytes.spec (GF := GF) (hG := hG) := fun s vs data_sl q data => by
  wp_start as ⟨Hs, Hdata, Hcap⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) (t := go.byte) s vs data_sl data q $$ [$Hs $Hcap $Hdata]
    as %s' ⟨Hs', Hcap', Hdata'⟩
  iapply HΦ
  iframe

end proof

end Perennial
