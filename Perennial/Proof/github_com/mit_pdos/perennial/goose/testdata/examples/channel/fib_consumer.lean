/-
The proof of `channel.fib_consumer`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.fib_consumer
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.fib_consumer.wp_proof
    (wp_fibonacci :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.fib_consumer.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make2 (V := w64) (W64 10) $$ [] as %c %γ ⟨#Hchan, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_spsc c (fun i v => iprop(⌜v = fib i.toNat⌝)) (fun sent => iprop(⌜sent = fibList 10⌝))
    γ $$ Hchan [Hown] with ⟨%γspsc, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  wp_apply chan.wp_cap (V := w64) c γ $$ Hchan
  rw [Hcap]
  wp_apply wp_fork $$ [Hprod]
  · rw [show fibList 10 = fibList (sint.nat (W64 10)) from rfl]
    wp_apply wp_fibonacci (W64 10) c γspsc (by decide) $$ [Hprod]
    · iframe # ∗
    itrivial
  wp_apply wp_slice_literal (V := w64) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  wp_auto
  ihave HI : (∃ (k : Nat) (iv : w64) (sl : GoSlice),
      "i" ∷ i_ptr ↦ iv ∗
      "Hcons" ∷ spscConsumer γspsc (fibList k) ∗
      "Hsl" ∷ sl ↦* fibList k ∗
      "results" ∷ results_ptr ↦ sl ∗
      "Hslcap" ∷ ownSliceCap w64 sl (DFrac.own 1) : IProp GF) $$ [i Hcons Hsl results Hslcap]
  · iexists 0, _, _
    rw [show fibList 0 = [] from rfl]
    iframe
  wp_for HI
  wp_apply wp_spsc_receive (t := go.int) γspsc c _ _ (fibList k) $$ [Hcons] as %v %ok H
  · iframe # ∗
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨%Hfl, %Hv⟩
    wp_auto
    wp_for_post
    rw [Hfl]
    iapply HΦ $$ Hsl
  · simp only [↓reduceIte]
    icases H with ⟨%Hfib, Hcons⟩
    wp_auto
    wp_apply wp_slice_literal (V := w64) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hslcap Hsl2] with %sl' ⟨Hsl, Hslcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists k + 1, _, sl'
    rw [fibList_length] at Hfib
    subst Hfib
    rw [fibList_succ k]
    simp only [Int.toNat_natCast]
    iframe

end proof

end Perennial
