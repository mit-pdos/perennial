/-
The proof of `sort.order2` over a `sort.Interface`: the proof of `slices.order2CmpFunc`
(`Perennial/Proof/slices/order2CmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.order2.wp_proof : sort.order2.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b swaps_l xs swaps xa xb Ha_bound Hb_bound => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_sorter_Less x own R xs b a xb xa Hb_bound Ha_bound Hxb Hxa $$ [$Hsrt $Hxs]
    as %r ⟨Hxs, %Hr⟩
  cases r
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => by simpa using Hr.2 h⟩
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 rfl⟩

end proof

end Perennial
