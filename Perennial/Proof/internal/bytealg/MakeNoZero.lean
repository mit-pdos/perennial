/-
The proof of `internal.bytealg.MakeNoZero`.
-/
module

public import Perennial.Spec.internal.bytealg.MakeNoZero

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `fillArbitrary i sl n` writes some bytes into `sl[i..n)`. -/
theorem wp_fillArbitrary (sl : GoSlice) (n : w64) (hn : sint.Z sl.len = sint.Z n) :
    ∀ (i : w64) (bs : List w8), 0 ≤ sint.Z i →
    {{ (sl ↦* bs ∗ ⌜bs.length = sint.nat n⌝ : IProp GF) }}
      (App (App (App (Val internal.bytealg.fillArbitrary) (Val #i)) (Val #sl)) (Val #n))
    {{ RET #(); ∃ bs' : List w8, ⌜bs'.length = sint.nat n⌝ ∗ sl ↦* bs' }} := by
  intro i bs hi
  unfold internal.bytealg.fillArbitrary
  iloeb as IH generalizing %i %bs %hi
  wp_start_folded as ⟨Hs, %hbs⟩
  wp_call
  wp_pures
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi, by omega⟩
    simp only [Hb, and_self, ↓reduceIte]
    wp_pures
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %x _
    wp_pures
    wp_apply_core wp_store_slice_index sl (sint.Z i) bs _ $$ [Hs]
    · iframe; ipureintro; rw [hbs]; simp only [sint.nat, sint.Z] at *; omega
    iintro Hs
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    iapply IH $$ %(i + W64 1) %_ %(by word) [Hs] HΦ
    iframe Hs
    ipureintro; simp only [List.length_set, hbs]
  · iapply HΦ
    iexists bs
    iframe
    ipureintro; exact hbs

/-- Proved from the model of `MakeNoZero` (`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.MakeNoZero.wp_proof :
    internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG) := fun n Hn => by
  wp_start
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  have Hmax : sint.Z (W64 internal.bytealg.maxAlloc) = internal.bytealg.maxAlloc := by
    unfold internal.bytealg.maxAlloc; word
  rw [decide_eq_false (show ¬ sint.Z (W64 internal.bytealg.maxAlloc) < sint.Z n by
    rw [Hmax]; omega)]
  wp_auto
  wp_apply wp_new_cap with %cap %Hcap
  wp_if_destruct
  · wp_apply wp_slice_make3 (V := w8) n n ⟨Hn.1, Int.le_refl _⟩
      (make_cap_ok (by rw [go.typeSize_w8]; unfold internal.bytealg.maxAlloc at Hn; omega))
      with %sl ⟨Hsl, Hsl_cap, -⟩
    ihave %Hlen := ownSlice_len $$ Hsl
    simp only [List.length_replicate] at Hlen
    wp_pures
    wp_apply wp_fillArbitrary sl n (by simp only [sint.nat, sint.Z] at *; omega) (W64 0) _ (by decide) $$ [Hsl]
      as ⟨%bs, %hbs, Hsl⟩
    · iframe; ipureintro; simp
    wp_pures
    iapply HΦ
    iexists bs
    iframe
    ipureintro; exact hbs
  · wp_apply wp_slice_make3 (V := w8) n cap ⟨Hn.1, Hcap⟩
      (make_cap_ok (by rw [go.typeSize_w8]; rw [Hmax] at *; unfold internal.bytealg.maxAlloc at *; omega))
      with %sl ⟨Hsl, Hsl_cap, -⟩
    ihave %Hlen := ownSlice_len $$ Hsl
    simp only [List.length_replicate] at Hlen
    wp_pures
    wp_apply wp_fillArbitrary sl n (by simp only [sint.nat, sint.Z] at *; omega) (W64 0) _ (by decide) $$ [Hsl]
      as ⟨%bs, %hbs, Hsl⟩
    · iframe; ipureintro; simp
    wp_pures
    iapply HΦ
    iexists bs
    iframe
    ipureintro; exact hbs

end proof

end Perennial
