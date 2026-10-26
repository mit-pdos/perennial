/-
The proof of `parallel_search_replace.worker`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Proof.sync.WaitGroupJoin

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker.wp_proof
    (wp_WaitGroup_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker.spec
      (GF := GF) (hG := hG) := fun γs ch wg x y => by
  wp_start as #Hchan
  wp_auto
  wp_apply wp_bag_receive γs ch (chanP wg x y) $$ Hchan as %s Hrcv
  ipersist y
  ipersist x
  ihave HH : (∃ s : GoSlice, "s" ∷ s_ptr ↦ s ∗ "Hrcv" ∷ chanP wg x y s : IProp GF) $$ [s Hrcv]
  · iexists s; iframe
  wp_for HH
  iNamed Hrcv
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "Hxs" ∷ s ↦* (searchReplace x y (xs.take (sint.nat i)) ++ xs.drop (sint.nat i)) ∗
      "%Hi_bound" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ xs.length⌝ : IProp GF) $$ [i Hxs]
  · iexists W64 0
    iframe i
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    simp only [searchReplace, List.map_nil, List.nil_append]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hne : i ≠ s.len := by
      intro h; subst h; simp [false_neq_true] at Hif
    have Hlt : sint.Z i < sint.Z s.len := by
      have : sint.nat i ≠ sint.nat s.len := by
        intro h; apply Hne; word
      word
    simp only [Hi_bound.1, Hlt, and_self, ↓reduceIte]
    list_elem xs (sint.nat i) as x'
    have Hlook := searchReplace_lookup x y xs (sint.nat i) x' Hx'_lookup
    have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    wp_apply wp_load_slice_index s (sint.Z i) _ _ x' Hi_bound.1 $$ [Hxs] with Hxs
    · iframe; ipureintro; exact Hlook
    have Hlen' : (xs.length : Int) = sint.Z s.len := by word
    by_cases Hx : x' = x
    · simp only [Hx, _root_.decide_true]
      wp_auto
      simp only [Hi_bound.1, Hlt, and_self, ↓reduceIte]
      wp_apply wp_store_slice_index s (sint.Z i) _ y $$ [Hxs] with Hxs
      · iframe; ipureintro; constructor
        · exact Hi_bound.1
        · simp only [List.length_append, searchReplace_length, List.length_take, List.length_drop]
          omega
      wp_for_post
      iframe
      iexists i + W64 1
      have := searchReplace_step x y xs (sint.nat i) x' Hx'_lookup
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hx)] at this
      rw [Hi1, ← this]
      iframe
      ipureintro; constructor <;> word
    · simp only [Hx, _root_.decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      rw [Hi1, ← searchReplace_step_ne x y xs (sint.nat i) x' Hx'_lookup Hx]
      iframe
      ipureintro; constructor <;> word
  · have Heq : i = s.len := by
      by_cases h : i = s.len
      · exact h
      · exfalso; apply Hif; simp [h]
    subst Heq
    simp
    have Hfull : sint.nat s.len = xs.length := by omega
    rw [Hfull, List.take_of_length_le (Nat.le_refl _), List.drop_length, List.append_nil]
    wp_auto
    wp_apply sync.join.WaitGroup.wp_Done_of wp_WaitGroup_Done (s ↦* searchReplace x y xs) wg $$ [Hwg_done Hxs]
    · iframe
    wp_for_post
    wp_apply wp_bag_receive γs ch (chanP wg x y) $$ Hchan as %s' Hrcv
    iframe
    unfold named
    iexists s'
    iframe

end proof

end Perennial
