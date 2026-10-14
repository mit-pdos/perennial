/-
The proof of `strings.Builder.WriteString`.
-/
module

public import Perennial.Spec.strings.Builder__WriteString
public import Perennial.Spec.strings.Builder__copyCheck
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Builder.WriteString.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG)) :
    strings.Builder.WriteString.spec (GF := GF) (hG := hG) := fun b s t => by
  wp_start as Hb
  unfold ownBuilder
  icases Hb with ⟨%addr, %buf, Hb, %Haddr, Hs, Hcap⟩
  wp_auto
  wp_apply wp_copyCheck b addr buf Haddr $$ [$Hb] as Hb
  wp_apply wp_string_to_bytes as %tsl ⟨Htsl, -⟩
  wp_apply wp_slice_append (V := w8) (t := go.byte) buf s tsl t (DFrac.own 1)
    $$ [Hs Hcap Htsl] as %buf' ⟨Hs', Hcap', -⟩
  · iframe
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  iapply HΦ
  iexists b, buf'
  iframe
  ipureintro
  exact Or.inr rfl

end proof

end Perennial
