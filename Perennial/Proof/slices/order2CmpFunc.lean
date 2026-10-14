/-
The proof of `slices.order2CmpFunc`.
-/
module

public import Perennial.Spec.slices.order2CmpFunc
public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.order2CmpFunc.wp_proof : slices.order2CmpFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b swaps_l cmp_code dq xs swaps xa xb Ha_bound Hb_bound
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have := lookup_lt_Some Hxa
  have := lookup_lt_Some Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z b) xs dq xb Hb_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs dq xa Ha_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa
  unfold cmpImplements
  wp_apply Hcmp with %r %Hr
  wp_if_destruct
  · iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 (by word)⟩
  · iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => Hif (by have := Hr.2 h; word)⟩

end proof

end Perennial
