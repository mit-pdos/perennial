/-
The proof of `errors.As` (its Go model, `goose/model/overlay/errors/wrap.go`: Go's `As`, its tree
walk `asWalk`).
-/
module

public import Perennial.Spec.errors.As
public import Perennial.Spec.errors.asWalk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

theorem errors.As.wp_proof
    (wp_asWalk : errors.asWalk.spec (GF := GF) (hG := hG)) :
    errors.As.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S err l T' _ _ T _ v hT hdec
    wp_start as ⟨#Htree, %HS, Hl⟩
    wp_auto
    cases err with
    | nil =>
      wp_auto
      iapply HΦ
      iframe
    | ok ii =>
      wp_auto
      wp_apply wp_asWalk.1 S ii l v hT hdec $$ [Hl] as %b %v' Hl
      · iframe; iframe #; ipureintro; exact HS
      iapply HΦ
      iframe
  · intro ii l T' _ _ T _ v hT hA htyped
    wp_start as Hl
    wp_auto
    wp_apply wp_asWalk.2.1 ii l v hT hA htyped $$ [$Hl] as %x ⟨Hl, %Hx⟩
    iapply HΦ
    iframe
    ipureintro; exact Hx
  · intro n err l T' _ _ T _ v hT
    wp_start as ⟨Hl, Hm⟩
    wp_auto
    cases err with
    | nil =>
      wp_auto
      iapply HΦ
      iframe
    | ok ii =>
      wp_auto
      wp_apply wp_asWalk.2.2 n ii l v hT $$ [$Hl $Hm] as Hl
      iapply HΦ
      iframe

end proof

end Perennial
