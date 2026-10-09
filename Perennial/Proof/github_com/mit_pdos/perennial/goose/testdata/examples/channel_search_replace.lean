/-
A parallel search-and-replace over a slice, with work items sent over a channel
(bag idiom) and completion tracked by a `sync.WaitGroup` (join idiom).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync_proof.waitgroup_join
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics] [package_sem : parallel_search_replace.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  build_get_is_pkg_init_wf

end init

structure SearchReplaceNames where
  wg : sync.WaitGroupNames
  wgAdded : GName

def searchReplace (x y : w64) (l : List w64) : List w64 :=
  l.map (fun a => if a = x then y else a)

@[simp] theorem searchReplace_length (x y : w64) (l : List w64) :
    (searchReplace x y l).length = l.length := by
  simp [searchReplace]

theorem searchReplace_lookup (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') :
    (searchReplace x y (xs.take i) ++ xs.drop i)[i]? = some x' := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 h).1
  have h3 : (searchReplace x y (xs.take i)).length = i := by simp; omega
  rw [List.getElem?_append_right (by omega), h3, Nat.sub_self, List.getElem?_drop, Nat.add_zero, h]

theorem searchReplace_step (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') :
    (searchReplace x y (xs.take i) ++ xs.drop i).set i (if x' = x then y else x') =
      searchReplace x y (xs.take (i + 1)) ++ xs.drop (i + 1) := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 h).1
  have h3 : (searchReplace x y (xs.take i)).length = i := by simp; omega
  rw [List.set_append_right _ _ (by omega), h3, Nat.sub_self, List.take_add_one, h,
    List.drop_eq_getElem_cons hi]
  simp only [Option.toList_some, List.set_cons_zero, searchReplace, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]

theorem searchReplace_step_ne (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') (hne : ¬ x' = x) :
    searchReplace x y (xs.take i) ++ xs.drop i =
      searchReplace x y (xs.take (i + 1)) ++ xs.drop (i + 1) := by
  rw [← searchReplace_step x y xs i x' h, ite_eq_right_iff.2 (fun h => absurd h hne),
    list_set_lookup_self _ _ _ (searchReplace_lookup x y xs i x' h)]

theorem searchReplace_take_append (x y : w64) (xs : List w64) (o n : Nat) (h : o ≤ n) :
    (searchReplace x y xs).take o ++ searchReplace x y ((xs.drop o).take (n - o)) =
      (searchReplace x y xs).take n := by
  have hn : n = o + (n - o) := by omega
  conv => rhs; rw [hn]
  unfold searchReplace
  rw [← List.map_take, ← List.map_take, ← List.map_append, ← List.take_add]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : parallel_search_replace.Assumptions]

local notation "pkg" =>
  pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

def chanP (wg : Loc) (x y : w64) (s : GoSlice) : IProp GF :=
  iprop(∃ xs : List w64,
    "Hxs" ∷ s ↦* xs ∗
    "Hwg_done" ∷ sync.join.ownDone wg (s ↦* (searchReplace x y xs)))

def waitgroupN : Namespace := nroot.@"waitgroup"

/-- An empty subslice is owned persistently. TODO: move to the slice theory. -/
theorem ownSlice_slice_empty (index : w64) (s : GoSlice) (xs : List w64)
    (h : 0 ≤ sint.Z index ∧ sint.Z index ≤ sint.Z s.cap) :
    (s ↦* xs : IProp GF) ⊢ □ (slice.slice s w64 index index ↦* ([] : List w64)) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · obtain ⟨rfl, rfl⟩ := H
    have hi : index = W64 0 := by simp only [slice.nil] at h; word
    subst hi
    imodintro
    ileft
    ipureintro
    refine ⟨?_, rfl⟩
    simp only [slice.slice, sliceIndexRef, slice.nil]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
    rfl
  · ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
    have hslice : slice.slice s w64 index index =
        slice.mk (sliceIndexRef w64 (sint.Z index) s) (W64 0) (s.cap - index) := by
      simp [slice.slice]
    rw [hslice]
    have hp : sliceIndexRef w64 (sint.Z index) s ≠ null :=
      fun hn => Hnn (go.arrayIndexRef_null_inv _ _ _ hn)
    imodintro
    iright
    isplit
    · exact array_empty (V := w64) _ _ hp
    · ipureintro; word

set_option goose.wp.extras true

theorem wp_worker (γs : ChanNames) (ch : Loc) (wg : Loc) (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "#Hchan" ∷ isChanBag γs ch (chanP wg x y) }}
      (App (App (App (App (Val (@! worker)) (Val #ch)) (Val #wg)) (Val #x)) (Val #y))
    {{ RET #(); True }} := by
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
    wp_apply sync.join.WaitGroup.wp_Done (s ↦* searchReplace x y xs) wg $$ [Hwg_done Hxs]
    · iframe
    wp_for_post
    wp_apply wp_bag_receive γs ch (chanP wg x y) $$ Hchan as %s' Hrcv
    iframe
    unfold named
    iexists s'
    iframe


theorem wp_SearchReplace (s : GoSlice) (xs : List w64) (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ s ↦* xs ∗
        ⌜(xs.length : Int) ≤ 2 ^ 63 - 1000⌝ ∗
        ⌜(xs.length : Int) ≤ (2 ^ 31 - 1) * 1000⌝ }}
      (App (App (App (Val (@! SearchReplace)) (Val #s)) (Val #x)) (Val #y))
    {{ RET #(); s ↦* (searchReplace x y xs) }} := by
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
  wp_apply chan.wp_make2 (V := GoSlice) (W64 4) $$ [] as %ch %γch_names ⟨#His_chan, %Hcap4, Hoc⟩
  · ipureintro; decide
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, H⟩
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
    wp_apply sync.join.WaitGroup.wp_Add
        (slice.slice s w64 offset no ↦*
          searchReplace x y ((xs.drop (sint.nat offset)).take (sint.nat no - sint.nat offset)))
        wg_ptr _ nadded $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; exact Hnadded'
    icases (ownSlice_split no s _ (xs.drop (sint.nat offset)) offset s.len
      ⟨Hoffset.1, by omega, by omega⟩).1 $$ Hs with ⟨Hsec, Hs⟩
    wp_auto
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
    wp_apply sync.join.WaitGroup.wp_Wait
        (slice.slice s w64 (W64 0) s.len ↦* (searchReplace x y xs).take (sint.nat s.len))
        nadded wg_ptr $$ [$Hwg] as ⟨>Hres, -⟩
    have Hfull : sint.nat s.len = (searchReplace x y xs).length := by
      rw [searchReplace_length]; omega
    rw [Hfull, List.take_length]
    iapply HΦ
    iapply (ownSlice_trivial_slice s _ _).2 $$ Hres

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

end Perennial
