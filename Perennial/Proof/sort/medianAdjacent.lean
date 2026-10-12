/-
The proof of `sort.medianAdjacent` over a `sort.Interface`: the proof of `slices.medianAdjacentCmpFunc`
(`Perennial/Proof/slices/medianAdjacentCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.medianAdjacent
public import Perennial.Spec.sort.median
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

theorem sort.medianAdjacent.wp_proof
    (wp_median : sort.median.spec (GF := GF) (hG := hG)) :
    sort.medianAdjacent.spec (GF := GF) (hG := hG) := fun {E} x own R _ a swaps_l xs swaps => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_median x own R (a - W64 1) a (a + W64 1) swaps_l xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

end proof

end Perennial
