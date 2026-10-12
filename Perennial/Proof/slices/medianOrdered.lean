/-
The proof of `slices.medianOrdered`.
-/
module

public import Perennial.Spec.slices.medianOrdered
public import Perennial.Spec.slices.order2Ordered
public import Perennial.Proof.slices.OrderedPartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.medianOrdered.wp_proof
    (wp_order2Ordered : slices.order2Ordered.spec (GF := GF) (hG := hG)) :
    slices.medianOrdered.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b c swaps_l dq xs swaps
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat a) as xa
  list_elem xs (sint.nat b) as xb
  list_elem xs (sint.nat c) as xc
  wp_apply wp_order2Ordered R data a b swaps_l dq xs swaps xa xb (by omega) (by omega)
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2Ordered R data b c swaps_l dq xs sw1 xb xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2Ordered R data a b swaps_l dq xs sw2 xa xb (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2Ordered R data a c swaps_l dq xs sw2 xa xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2Ordered R data a c swaps_l dq xs sw1 xa xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2Ordered R data b a swaps_l dq xs sw2 xb xa (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2Ordered R data b c swaps_l dq xs sw2 xb xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

end proof

end Perennial
