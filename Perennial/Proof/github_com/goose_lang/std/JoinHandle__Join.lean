/-
The proof of `github.com/goose-lang/std.(*JoinHandle).Join`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.JoinHandle__Join
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Cond__Wait
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.JoinHandle.Join.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Cond_Wait : sync.Cond.Wait.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.JoinHandle.Join.spec (GF := GF) (hG := hG) := fun l P => by
  wp_start as #Hjh
  unfold isJoinHandle
  iNamed Hjh
  wp_auto
  wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  ihave HI : (∃ done_b : Bool,
      "locked" ∷ sync.ownMutex mu_l ∗
      "done" ∷ typedPointsto (structFieldRef JoinHandle go!"done" l) done_b (DFrac.own 1) ∗
      "HP" ∷ jhP done_b P : IProp GF) $$ [Hlocked done_b HP]
  · iexists done_b; iframe
  wp_for HI
  cases done_b with
  | false =>
    wp_auto
    ihave #Hlk := Mutex_is_Locker_of wp_Mutex_Lock wp_Mutex_Unlock mu_l (jhInv l P) $$ [] Hlock
    · iPkgInit
    wp_apply wp_Cond_Wait cond_l _ iprop(sync.ownMutex mu_l ∗ jhInv l P)
      $$ [$Hcond $Hlk locked done HP] as ⟨Hlocked, Hlinv⟩
    · iframe locked; iexists false; iframe
    iNamed Hlinv
    wp_for_post
    iframe
    iexists done_b
    iframe
  | true =>
    wp_auto
    wp_for_post
    wp_apply wp_Mutex_Unlock $$ [$Hlock $locked done]
    · inext; iexists false; iframe done; unfold jhP; simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    iapply HΦ
    unfold jhP
    simp only [↓reduceIte]
    iexact HP

end proof

end Perennial
