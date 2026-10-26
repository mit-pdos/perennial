/-
The proof of `sort.xorshift.Next` (as `Perennial/Proof/slices/xorshift__Next.lean`).
-/
module

public import Perennial.Spec.sort.xorshift__Next
public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.xorshift.Next.wp_proof : sort.xorshift.Next.spec (GF := GF) (hG := hG) := fun r v => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as Hr
  wp_auto
  wp_end

end proof

end Perennial
