/-
The proof of `parallel_search_replace.SearchReplace`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.SearchReplace
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.SearchReplace.wp_proof
    (wp_worker :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker.spec
        (GF := GF) (hG := hG))
    (wp_WaitGroup_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_WaitGroup_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.SearchReplace.spec
      (GF := GF) (hG := hG) := fun s xs x y => by
  -- The first overflow: implementation adds 1000 at a time, potentially
  -- surpassing the slice length before clamping. If it goes negative, then the
  -- clamping doesn't work. This inequality is technically implied by the second;
  -- keeping for documentation (and e.g. workRange can change).
  -- The second overflow: if `len(xs)` is bigger than `(2^31-1)*workRange`, then
  -- Add() will be called *more* than 2^31-1 times, potentially overflowing the
  -- internal waitgroup counter.
  wp_start as ⟨Hs, %Hoverflow1, %Hoverflow2⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hcap := ownSlice_wf _ _ _ $$ Hs
  wp_if_destruct
  · have : xs = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    subst this
    iapply HΦ
    simp only [searchReplace, List.map_nil]
    iexact Hs
  wp_apply +noauto chan.wp_make2 (V := GoSlice) (W64 4) $$ [] as %ch %γch_names ⟨#His_chan, %Hcap4, Hoc⟩
  · ipureintro; decide
  -- (the WaitGroup is allocated explicitly, for its alignment, `init_WaitGroup`)
  wp_pures
  wp_alloc c_ptr as c
  wp_pures
  wp_store
  wp_pures
  wp_apply_core wp_alloc _
  iintro %wg_ptr ⟨wg, %wg_aligned⟩
  wp_auto
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr wg_aligned $$ wg with ⟨%γwg, H⟩
  imod sync.join.init wg_ptr γwg $$ H with Hwg
  imod start_bag (chanP wg_ptr x y) (.Buffered []) ch γch_names trivial $$ His_chan Hoc with #Hchan
  ihave HH : (∃ i : w64, "i" ∷ i_ptr ↦ i : IProp GF) $$ [i]
  · iexists _; iexact i
  wp_for HH
  wp_if_destruct
  · wp_apply wp_fork $$ []
    · wp_apply wp_worker γch_names ch wg_ptr x y $$ [Hchan]
      · iexact Hchan
      itrivial
    wp_for_post
    iframe
    iexists _
    iframe
  have Heq : i = W64 8 := by
    by_cases h : i = W64 8
    · exact h
    · have h' : ¬ i = 8#64 := h
      exfalso; apply Hif; simp [h']
  subst Heq
  simp only [_root_.decide_true, Bool.not_true, ↓reduceIte]
  wp_auto
  -- the work-distribution loop
  ihave #Hempty := ownSlice_slice_empty (W64 0) s xs ⟨by decide, by word⟩ $$ Hs
  ihave HH : (∃ (offset : w64) (nadded : w32),
      "offset" ∷ offset_ptr ↦ offset ∗
      "Hs" ∷ slice.slice s w64 offset s.len ↦* xs.drop (sint.nat offset) ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr nadded
        (slice.slice s w64 (W64 0) offset ↦* (searchReplace x y xs).take (sint.nat offset)) ∗
      "%Hoffset" ∷ ⌜0 ≤ sint.Z offset ∧ sint.nat offset ≤ xs.length⌝ ∗
      "%Hnadded" ∷ ⌜(0 ≤ sint.Z nadded ∧ 1000 * sint.Z nadded ≤ sint.Z offset) ∨
        sint.nat offset = xs.length⌝ : IProp GF) $$ [offset Hs Hwg]
  · iexists W64 0, W32 0
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    iframe offset
    isplitl [Hs]
    · iapply (ownSlice_trivial_slice s _ xs).1 $$ Hs
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro -
      iexact Hempty
    ipureintro
    exact ⟨⟨by decide, Nat.zero_le _⟩, Or.inl ⟨by decide, by decide⟩⟩
  ipersist s
  wp_for HH
  wp_if_destruct
  · have Hne : offset ≠ s.len := by
      intro h; subst h; simp [false_neq_true] at Hif
    have Hlt : sint.Z offset < sint.Z s.len := by
      have : sint.nat offset ≠ sint.nat s.len := by
        intro h; apply Hne; word
      word
    have Hadd : sint.Z (offset + W64 1000) = sint.Z offset + 1000 := by word
    obtain ⟨no, hno⟩ : ∃ no : w64,
        no = if sint.Z s.len < sint.Z (offset + W64 1000) then s.len else offset + W64 1000 :=
      ⟨_, rfl⟩
    have Hno : sint.Z no = min (sint.Z offset + 1000) (sint.Z s.len) := by
      rw [hno]
      by_cases hc : sint.Z s.len < sint.Z (offset + W64 1000)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; omega
      · rw [ite_eq_right_iff.2 (fun h => absurd h hc)]; omega
    have hoffN : (sint.nat offset : Int) = sint.Z offset := Int.toNat_of_nonneg Hoffset.1
    have hno0 : 0 ≤ sint.Z no := by omega
    have hnoN : (sint.nat no : Int) = sint.Z no := Int.toNat_of_nonneg hno0
    have hlenN : (sint.nat s.len : Int) = sint.Z s.len := Int.toNat_of_nonneg Hlen.2
    wp_bind (If _ _ _)
    iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ nextOffset_ptr ↦ no)) $$ [nextOffset]
    · by_cases hc : sint.Z s.len < sint.Z (offset + W64 1000)
      · simp only [hc, _root_.decide_true]
        wp_auto
        rw [hno, ite_eq_left_of_eq_true _ _ (eq_true hc)]
        iframe
        ipureintro; rfl
      · simp only [hc, _root_.decide_false]
        wp_auto
        rw [hno, ite_eq_right_iff.2 (fun h => absurd h hc)]
        iframe
        ipureintro; rfl
    iintro %v ⟨%Hv, nextOffset⟩
    subst Hv
    wp_auto
    have Hb : 0 ≤ sint.Z offset ∧ sint.Z offset ≤ sint.Z no ∧ sint.Z no ≤ sint.Z s.cap :=
      ⟨Hoffset.1, by omega, by omega⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hb)]
    wp_auto
    have Hnadded' : sint.Z nadded < 2 ^ 31 - 1 := by
      rcases Hnadded with H | H
      · have : (xs.length : Int) = sint.Z s.len := by word
        omega
      · exfalso; apply Hne; word
    wp_apply sync.join.WaitGroup.wp_Add_of wp_WaitGroup_Add
        (slice.slice s w64 offset no ↦*
          searchReplace x y ((xs.drop (sint.nat offset)).take (sint.nat no - sint.nat offset)))
        wg_ptr _ nadded $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; exact Hnadded'
    icases (ownSlice_split no s _ (xs.drop (sint.nat offset)) offset s.len
      ⟨Hoffset.1, by omega, by omega⟩).1 $$ Hs with ⟨Hsec, Hs⟩
    try wp_auto
    wp_apply wp_bag_send γch_names ch (slice.slice s w64 offset no) (chanP wg_ptr x y)
      $$ [Hsec Hdone]
    · iframe #
      unfold chanP
      iexists _
      iframe
    wp_for_post
    iframe
    iexists no, nadded + W32 1
    rw [List.drop_drop, show sint.nat offset + (sint.nat no - sint.nat offset) = sint.nat no by omega]
    iframe offset Hs
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro ⟨Hpre, Hsuf⟩
      ihave Hc := ownSlice_combine offset s _ _ _ (W64 0) no
        ⟨by simp only [List.length_take, searchReplace_length]
            rw [show sint.nat (W64 0) = 0 from rfl]; omega,
          by decide, Hoffset.1, by omega⟩
        $$ Hpre Hsuf
      rw [searchReplace_take_append x y xs _ _ (by omega)]
      iexact Hc
    ipureintro
    have : (xs.length : Int) = sint.Z s.len := by word
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    by_cases hc : sint.Z offset + 1000 ≤ sint.Z s.len
    · left
      have : sint.Z (nadded + W32 1) = sint.Z nadded + 1 := by word
      rcases Hnadded with H | H
      · omega
      · exfalso; apply Hne; word
    · right; omega
  · have Heq : offset = s.len := by
      by_cases h : offset = s.len
      · exact h
      · exfalso; apply Hif; simp [h]
    subst Heq
    simp only [_root_.decide_true, Bool.not_true, ↓reduceIte]
    wp_auto
    wp_apply sync.join.WaitGroup.wp_Wait_of wp_WaitGroup_Wait
        (slice.slice s w64 (W64 0) s.len ↦* (searchReplace x y xs).take (sint.nat s.len))
        nadded wg_ptr $$ [$Hwg] as ⟨>Hres, -⟩
    have Hfull : sint.nat s.len = (searchReplace x y xs).length := by
      rw [searchReplace_length]; omega
    rw [Hfull, List.take_length]
    iapply HΦ
    iapply (ownSlice_trivial_slice s _ _).2 $$ Hres

end proof

end Perennial
