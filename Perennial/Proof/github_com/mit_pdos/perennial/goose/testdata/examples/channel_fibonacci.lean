/-
A producer sends the Fibonacci numbers over a single-producer single-consumer
channel (`go.dev/tour/concurrency/4`).
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Spsc

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-- The Fibonacci numbers (wrapping on overflow). -/
def fib : Nat → w64
  | 0 => W64 0
  | 1 => W64 1
  | n + 2 => fib (n + 1) + fib n

def fibList (n : Nat) : List w64 := (List.range n).map fib

theorem fibList_succ (n : Nat) : fibList (n + 1) = fibList n ++ [fib n] := by
  simp [fibList, List.range_succ]

theorem fibList_length (n : Nat) : (fibList n).length = n := by
  simp [fibList]

theorem fib_succ (k : Nat) :
    fib (k + 1) = match k with | 0 => W64 1 | k' + 1 => fib (k' + 1) + fib k' := by
  cases k <;> rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem wp_fibonacci (n : w64) (c0 : Loc) (γ : SpscNames) (Hn : 0 < sint.Z n) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        isSpsc γ c0 (fun i v => iprop(⌜v = fib i.toNat⌝))
          (fun sent => iprop(⌜sent = fibList (sint.nat n)⌝)) ∗
        spscProducer γ ([] : List w64) }}
      (App (App (Val (@! fibonacci)) (Val #n)) (Val #c0))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hspsc, Hprod⟩
  wp_auto
  ihave HI : (∃ (i : Nat) (sent : List w64),
      "Hprod" ∷ spscProducer γ sent ∗
      "x" ∷ x_ptr ↦ fib i ∗
      "y" ∷ y_ptr ↦ fib (i + 1) ∗
      "i" ∷ i_ptr ↦ W64 i ∗
      "%Hil" ∷ ⌜i = sent.length⌝ ∗
      "%Hsl" ∷ ⌜sent = fibList i⌝ ∗
      "%Hi" ∷ ⌜i ≤ sint.nat n⌝ : IProp GF) $$ [Hprod x y i]
  · iexists 0, []
    rw [show fib 0 = W64 0 from rfl, show fib (0 + 1) = W64 1 from rfl]
    iframe
    ipureintro; exact ⟨rfl, rfl, Nat.zero_le _⟩
  wp_for HI
  wp_if_destruct
  · wp_apply wp_spsc_send (t := go.int) γ c0 _ _ sent (fib i) $$ [Hprod] as Hprod
    · iframe # ∗
      ipureintro; subst Hil; simp
    wp_for_post
    iframe
    iexists i + 1, sent ++ [fib i]
    rw [show fib (i + 1 + 1) = fib i + fib (i + 1) from (BitVec.add_comm _ _),
      show (W64 (i : Int) + W64 1 : w64) = W64 ((i + 1 : Nat) : Int) by word]
    iframe
    ipureintro
    have : sint.Z (W64 (i : Int)) = i := by word
    refine ⟨by simp [Hil], by rw [Hsl, fibList_succ], by word⟩
  · have hi : i = sint.nat n := by
      have : sint.Z (W64 (i : Int)) = i := by word
      word
    wp_apply wp_spsc_close (t := go.int) γ c0 _ _ sent $$ [Hprod]
    · iframe # ∗
      ipureintro; rw [Hsl, hi]
    wp_end

set_option maxHeartbeats 400000 in
theorem wp_fib_consumer :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! fib_consumer)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* fibList 10 }} := by
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

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
