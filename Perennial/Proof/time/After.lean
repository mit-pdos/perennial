/-
The proof of `time.After` (over its trusted model, `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.After

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- The timer's deadline `w` (Go's `when(d)` over the reading `x`) is reached only once the clock is
`d` past `T = max n x` (`x` is at least `n` unless the clock has saturated at `clockMax`). -/
theorem time.after_when_enc (n : Int) (x d w y : w64)
    (hx : time.clockEnc n ≤ time.clockEnc (sint.Z x))
    (hw : (sint.Z d ≤ 0 ∧ w = x) ∨
      (0 < sint.Z d ∧ sint.Z (x + d) < 0 ∧ w = W64 (2 ^ 63 - 1)) ∨
      (0 < sint.Z d ∧ 0 ≤ sint.Z (x + d) ∧ w = x + d))
    (hy : sint.Z w ≤ sint.Z y) :
    time.clockEnc (max n (sint.Z x) + sint.Z d) ≤ time.clockEnc (sint.Z y) := by
  unfold time.clockEnc time.clockMax at *
  have : -2 ^ 63 ≤ sint.Z x ∧ sint.Z x < 2 ^ 63 := by word
  have : -2 ^ 63 ≤ sint.Z y ∧ sint.Z y < 2 ^ 63 := by word
  have : -2 ^ 63 ≤ sint.Z d ∧ sint.Z d < 2 ^ 63 := by word
  rcases hw with ⟨hd, rfl⟩ | ⟨hd, ht, rfl⟩ | ⟨hd, ht, rfl⟩
  · omega
  · have : sint.Z (W64 (2 ^ 63 - 1)) = 2 ^ 63 - 1 := by decide
    omega
  · have hsum : sint.Z (x + d) = sint.Z x + sint.Z d := by word
    omega

theorem time.After.wp_proof :
    time.After.spec (GF := GF) (hG := hG) := by
  intro d n Ψ
  wp_start as ⟨#Hlb, HΨ⟩
  wp_apply wp_ArbitraryInt as %c -
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_if_destruct
  all_goals
    wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
    · ipureintro; decide
    wp_apply time.wp_runtimeClockNow n $$ Hlb as %x ⟨%Hx, #Hlbx⟩
    imod start_bag (fun _ => Ψ (max n (sint.Z x))) _ ch γ trivial $$ His Hown with #Hch
    wp_pures
    -- `when(d)`, in its three cases
    wp_if_destruct
    rotate_left
    wp_if_destruct
    all_goals
      wp_bind (Fork _)
      iapply wp_fork $$ [HΨ]
      · inext
        wp_pures
        wp_apply time.wp_runtimeClockWaitUntil (sint.Z x) _ $$ Hlbx as %y ⟨%Hy, #Hlby⟩
        ihave #HT := time.clockLb_enc (GF := GF) (time.after_when_enc n x d _ y Hx
          (by first
            | exact Or.inl ⟨by word, rfl⟩
            | exact Or.inr (Or.inl ⟨by word, by word, rfl⟩)
            | exact Or.inr (Or.inr ⟨by word, by word, rfl⟩)) Hy) $$ Hlby
        ihave HΨT := HΨ $$ %(max n (sint.Z x)) %(by omega) HT
        wp_apply time.wp_arbitraryTime as %tm -
        wp_apply wp_bag_send $$ [$Hch $HΨT]
        itrivial
      inext
      wp_pures
      iapply HΦ $$ %ch %γ %(max n (sint.Z x))
      isplitr
      · ipureintro; omega
      iframe Hch
      iapply time.clockLb_enc (by unfold time.clockEnc at *; omega) $$ Hlbx
