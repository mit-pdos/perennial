/-
The proof of `crypto/sha1.Sum`.
-/
module

public import Perennial.Spec.crypto.sha1.Sum
public import Perennial.Spec.crypto.internal.fips140only.Enforced
public import Perennial.Spec.crypto.sha1.digest__Reset
public import Perennial.Spec.crypto.sha1.digest__Write
public import Perennial.Spec.crypto.sha1.digest__checkSum

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

theorem crypto.sha1.Sum.wp_proof
    (wp_Enforced : crypto.internal.fips140only.Enforced.spec (GF := GF) (hG := hG))
    (wp_Reset : crypto.sha1.digest.Reset.spec (GF := GF) (hG := hG))
    (wp_Write : crypto.sha1.digest.Write.spec (GF := GF) (hG := hG))
    (wp_checkSum : crypto.sha1.digest.checkSum.spec (GF := GF) (hG := hG)) :
    crypto.sha1.Sum.spec (GF := GF) (hG := hG) := by
  intro s dq data Hoff
  wp_start as Hs
  wp_auto
  wp_apply wp_Enforced as %b %Hb
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (Hb rfl) (crypto.fips140.godebugFips140_ne_only Hoff)
  subst hb
  wp_auto
  wp_apply wp_Reset $$ [d] as ⟨%v1, d, %Hv1⟩
  · iexact d
  try wp_auto
  wp_apply (wp_Write _ v1 [] s dq data Hoff Hv1.1) $$ [d Hs] as ⟨%v2, d, %Hv2, Hs⟩
  · iframe
  wp_apply (wp_checkSum _ v2 _ Hoff Hv2) $$ [d] as ⟨%v3, d⟩
  · iexact d
  simp only [List.nil_append]
  wp_end

end proof

end Perennial
