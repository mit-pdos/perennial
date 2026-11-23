/-
The proof of `math/rand.Rand.Intn`.
-/
module

public import Perennial.Spec.math.rand.Rand__Intn
public import Perennial.Spec.math.rand.Rand__Int31n
public import Perennial.Spec.math.rand.Rand__Int63n

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.Rand.Intn.wp_proof
    (wp_Int31n : math.rand.Rand.Int31n.spec (GF := GF) (hG := hG))
    (wp_Int63n : math.rand.Rand.Int63n.spec (GF := GF) (hG := hG)) :
    math.rand.Rand.Intn.spec (GF := GF) (hG := hG) := by
  intro r n
  wp_start as ⟨#Hr, %Hn⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · have Hn32 : sint.Z (W32 (sint.Z n)) = sint.Z n := by word
    wp_apply wp_Int31n $$ [Hr] as %x %Hx
    · iframe Hr; ipureintro; rw [Hn32]; exact Hn
    iapply HΦ
    ipureintro
    rw [Hn32] at Hx
    word
  · wp_apply wp_Int63n $$ [Hr] as %x %Hx
    · iframe Hr; ipureintro; exact Hn
    try wp_auto
    iapply HΦ
    ipureintro
    word

end proof

end Perennial
