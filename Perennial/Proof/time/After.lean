/-
The proof of `time.After`.
-/
module

public import Perennial.Spec.time.After
public import Perennial.Spec.time.makeTimerChan
public import Perennial.Spec.time.runtimeClockNow
public import Perennial.Spec.time.whenAt
public import Perennial.Spec.time.checkWhen
public import Perennial.Spec.time.runtimeClockWaitUntil
public import Perennial.Spec.time.sendTimes

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
`d` past `T = max n x` (`x` is at least `n` unless `n` exceeds `clockMax`, the clock's largest
value). -/
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

/-- The deadline is positive: the clock's reading `x` is, and so is a saturated sum. -/
theorem time.after_when_pos (x d w : w64) (hx : 0 < sint.Z x)
    (hw : (sint.Z d ≤ 0 ∧ w = x) ∨
      (0 < sint.Z d ∧ sint.Z (x + d) < 0 ∧ w = W64 (2 ^ 63 - 1)) ∨
      (0 < sint.Z d ∧ 0 ≤ sint.Z (x + d) ∧ w = x + d)) :
    0 < sint.Z w := by
  rcases hw with ⟨hd, rfl⟩ | ⟨hd, ht, rfl⟩ | ⟨hd, ht, rfl⟩
  · exact hx
  · decide
  · word

theorem time.After.wp_proof
    (wp_makeTimerChan : time.makeTimerChan.spec (GF := GF) (hG := hG))
    (wp_runtimeClockNow : time.runtimeClockNow.spec (GF := GF) (hG := hG))
    (wp_whenAt : time.whenAt.spec (GF := GF) (hG := hG))
    (wp_checkWhen : time.checkWhen.spec (GF := GF) (hG := hG))
    (wp_runtimeClockWaitUntil : time.runtimeClockWaitUntil.spec (GF := GF) (hG := hG))
    (wp_sendTimes : time.sendTimes.spec (GF := GF) (hG := hG)) :
    time.After.spec (GF := GF) (hG := hG) := by
  intro d n Ψ
  wp_start as ⟨#Hlb, HΨ⟩
  wp_auto
  wp_apply wp_makeTimerChan as %ch %γ Hmk
  wp_apply wp_runtimeClockNow n $$ Hlb as %x ⟨%Hx, %Hx0, #Hlbx⟩
  imod Hmk $$ %(fun _ => Ψ (max n (sint.Z x))) with #Hch
  wp_apply wp_whenAt as %w %Hw
  wp_apply wp_checkWhen $$ []
  · ipureintro
    exact ⟨time.after_when_pos x d w Hx0 Hw, by decide⟩
  -- `c` and `w` are read by the goroutines, and written by neither
  ipersist c
  ipersist w
  wp_bind (Fork _)
  iapply wp_fork $$ [HΨ]
  · inext
    wp_auto
    wp_apply wp_runtimeClockWaitUntil (sint.Z x) w $$ Hlbx as %y ⟨%Hy, #Hlby⟩
    ihave #HT := time.clockLb_enc (GF := GF) (time.after_when_enc n x d w y Hx Hw Hy) $$ Hlby
    ihave HΨT := HΨ $$ %(max n (sint.Z x)) %(by omega) HT
    wp_apply (wp_sendTimes ch γ (Ψ (max n (sint.Z x))) (W64 0) (W64 0)) $$ [HΨT]
    · iframe #
      iexact HΨT
    itrivial
  inext
  wp_auto
  iapply HΦ $$ %ch %γ %(max n (sint.Z x))
  isplitr
  · ipureintro; omega
  iframe Hch
  iapply time.clockLb_enc (by unfold time.clockEnc at *; omega) $$ Hlbx

end proof

end Perennial
