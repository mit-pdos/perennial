/-
The proof of `crypto/sha1.block`.
-/
module

public import Perennial.Spec.crypto.sha1.block
public import Perennial.Spec.crypto.sha1.blockGeneric

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

theorem crypto.sha1.block.wp_proof
    (wp_blockGeneric : crypto.sha1.blockGeneric.spec (GF := GF) (hG := hG)) :
    crypto.sha1.block.spec (GF := GF) (hG := hG) := by
  intro dig p dq bs h
  wp_start as ⟨Hh, Hp⟩
  wp_auto
  wp_apply wp_blockGeneric $$ [$Hh $Hp] as ⟨Hh, Hp⟩
  wp_end

end proof

end Perennial
