/-
The proof of `sort.median` over a `sort.Interface`: the proof of `slices.medianCmpFunc`
(`Perennial/Proof/slices/medianCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.median
public import Perennial.Spec.sort.order2
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.sort.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.median.wp_proof
    (wp_order2 : sort.order2.spec (GF := GF) (hG := hG)) :
    sort.median.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b c swaps_l xs swaps => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat a) as xa
  list_elem xs (sint.nat b) as xb
  list_elem xs (sint.nat c) as xc
  wp_apply wp_order2 x own R a b swaps_l xs swaps xa xb (by omega) (by omega)
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2 x own R b c swaps_l xs sw1 xb xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2 x own R a b swaps_l xs sw2 xa xb (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 x own R a c swaps_l xs sw2 xa xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2 x own R a c swaps_l xs sw1 xa xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2 x own R b a swaps_l xs sw2 xb xa (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 x own R b c swaps_l xs sw2 xb xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

end proof

end Perennial
