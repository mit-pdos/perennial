/-
The proof of `channel.fibonacci`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.fibonacci.spec
      (GF := GF) (hG := hG) := fun n c0 γ Hn => by
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

end proof

end Perennial
