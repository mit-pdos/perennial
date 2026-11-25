/-
The proof of `time.runtimeClockNow`.
-/
module

public import Perennial.Spec.time.runtimeClockNow
public import Perennial.Spec.time.runtimeNano
public import Perennial.Spec.sync.atomic.LoadInt64
public import Perennial.Spec.sync.atomic.CompareAndSwapInt64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.runtimeClockNow.wp_proof
    (wp_LoadInt64 : sync.atomic.LoadInt64.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapInt64 : sync.atomic.CompareAndSwapInt64.spec (GF := GF) (hG := hG))
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG)) :
    time.runtimeClockNow.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as #Hlb
  unfold time.clockLb
  icases Hlb with ⟨%γ, #Hc, #Hlb⟩
  ihave #Hc' := Hc
  unfold time.isRuntimeClock
  icases Hc' with ⟨#Hatomic, #Hinv⟩
  wp_auto
  wp_for
  -- `c`: the clock now
  wp_apply_core (wp_LoadInt64 (globalAddr time.runtimeClock) (DFrac.own 1)) $$ [] [-]
  · iexact Hatomic
  iinv Hinv with ⟨%c, >Hl, >%Hc0, >Hauth⟩ Hclose
  ihave %Hnc := monoNatLbOwn_valid γ 1 _ _ $$ Hauth Hlb
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists c
  iframe Hl
  iintro Hl
  imod Hmask with -
  imod Hclose $$ [Hl Hauth] with -
  · inext; iexists c; iframe; ipureintro; exact Hc0
  imodintro
  wp_auto
  wp_apply wp_runtimeNano as %x %Hx
  wp_if_destruct
  · -- `c ≤ x`: advance the clock to `x`, if it is still `c`
    wp_apply_core (wp_CompareAndSwapInt64 (globalAddr time.runtimeClock) c x) $$ [] [-]
    · iexact Hatomic
    iinv Hinv with ⟨%c', >Hl, >%Hc0', >Hauth⟩ Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists c', (DFrac.own 1)
    iframe Hl
    isplitr
    · ipureintro; split <;> rfl
    iintro Hl
    imod Hmask with -
    by_cases hc : c' = c
    · subst hc
      rw [if_pos rfl, decide_eq_true rfl]
      imod mono_nat_own_update (time.clockEnc (sint.Z x)) (time.clockEnc_mono (by word)) $$ Hauth
        with ⟨Hauth, #Hlbx⟩
      imod Hclose $$ [Hl Hauth] with -
      · inext; iexists x; iframe; ipureintro; word
      imodintro
      wp_auto
      wp_for_post
      iapply HΦ
      isplitr
      · ipureintro
        have := time.clockEnc_mono (a := sint.Z c') (b := sint.Z x) (by word)
        omega
      isplitr
      · ipureintro; exact Hx
      iexists γ
      iframe #
    · rw [if_neg hc, decide_eq_false hc]
      imod Hclose $$ [Hl Hauth] with -
      · inext; iexists c'; iframe; ipureintro; exact Hc0'
      imodintro
      wp_auto
      wp_for_post
      iframe
  · wp_for_post
    iframe

end proof

end Perennial
