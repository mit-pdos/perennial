/-
The proof of `errors.Is`.
-/
module

public import Perennial.Spec.errors.Is
public import Perennial.Spec.errors.is_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- Proved from the trusted model of `Is` (`Perennial/TrustedCode/errors.lean`) and
`is`'s spec. -/
theorem errors.Is.wp_proof
    (wp_is : errors.is.spec (GF := GF) (hG := hG)) :
    errors.Is.spec (GF := GF) (hG := hG) := by
  intro S M err target htarget htyped
  wp_start as ⟨#Htree, %HS⟩
  wp_auto
  cases err with
  | nil =>
    dsimp only
    wp_auto
    cases target with
    | nil =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok tii =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ _ _ h => (by cases h), fun _ _ _ h => absurd rfl h⟩
  | ok ii =>
    cases target with
    | nil =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok tii =>
      dsimp only
      wp_auto
      obtain ⟨T, l, hT, hl⟩ := htarget tii rfl
      (try wp_auto)
      rw [show (go!"errors.is" : GoString) = is' from rfl]
      wp_apply wp_is S M (interface.ok ii) (interface.ok tii) true HS
        (fun _ => ⟨⟨tii, rfl, T, l, hT, hl⟩, htyped⟩) $$ [] as %b ⟨%Hb1, %Hb2⟩
      · iframe #
      iapply HΦ
      ipureintro
      refine ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h _ heq => ?_,
        fun _ _ _ _ hb => Hb1 hb⟩
      cases b
      · exact absurd heq (Hb2 rfl rfl (by simp))
      · rfl

end proof

end Perennial
