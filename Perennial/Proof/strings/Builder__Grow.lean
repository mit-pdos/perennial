/-
The proof of `strings.Builder.Grow`.
-/
module

public import Perennial.Spec.strings.Builder__Grow
public import Perennial.Spec.strings.Builder__copyCheck
public import Perennial.Spec.strings.Builder__grow_

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

theorem strings.Builder.Grow.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG))
    (wp_grow : strings.Builder.grow.spec (GF := GF) (hG := hG)) :
    strings.Builder.Grow.spec (GF := GF) (hG := hG) := fun b addr buf s n Haddr Hn Hgrow => by
  wp_start as ⟨Hb, Hs, Hcap⟩
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_auto
  wp_apply wp_copyCheck b addr buf Haddr $$ [$Hb] as Hb
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  by_cases hg : sint.Z (buf.cap - buf.len) < sint.Z n
  · rw [decide_eq_true hg]
    wp_auto
    wp_apply wp_grow b b buf s n ⟨Hn, Hgrow (by word)⟩ $$ [Hb Hs Hcap]
      as ⟨%buf', Hb, Hs, Hcap⟩
    · iframe
    iapply HΦ
    unfold ownBuilder
    iexists b, buf'
    iframe
    ipureintro
    exact Or.inr rfl
  · rw [decide_eq_false hg]
    wp_auto
    iapply HΦ
    unfold ownBuilder
    iexists b, buf
    iframe
    ipureintro
    exact Or.inr rfl

end proof

end Perennial
