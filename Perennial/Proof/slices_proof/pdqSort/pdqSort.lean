/-
Port of `new/proof/slices_proof/pdqSort/pdqSort.v`: the spec of
`pdqsortCmpFunc` (and `reverseRangeCmpFunc`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.slices
import Perennial.GeneratedProof.slices
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.slices_proof.pdqSort.sort_basics
import Perennial.Proof.slices_proof.pdqSort.partition
import Perennial.Proof.slices_proof.pdqSort.insertionSort
import Perennial.Proof.slices_proof.pdqSort.heapSort

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section pure
variable {E : Type} (R : E → E → Prop)

def IsPartiallySortedSeg (l : List E) (a b : Nat) (a1 b1 : Nat) : Prop :=
  ∀ (i j : Nat) xi xj, (a ≤ i ∧ i < j) ∧ j < b →
    i < a1 ∨ j ≥ b1 →
    l[i]? = some xi → l[j]? = some xj → ¬ R xj xi

/-- An element of `xs'` either sits outside `[av, bv)` (where `xs` and `xs'`
agree) or comes from some index of `xs` inside `[av, bv)`. -/
theorem outsideSame_lookup {T : Type} (xs xs' : List T) (av bv k : Nat) (x : T)
    (Hsame : OutsideSame xs xs' av bv) (Hperm : xs ≡ₚ xs') (Hb : bv ≤ xs.length)
    (Hk : xs'[k]? = some x) :
    ((k < av ∨ k ≥ bv) ∧ xs[k]? = some x) ∨
    ((av ≤ k ∧ k < bv) ∧ ∃ k0, xs[k0]? = some x ∧ av ≤ k0 ∧ k0 < bv) := by
  by_cases h : k < av ∨ k ≥ bv
  · left; exact ⟨h, (Hsame k h).trans Hk⟩
  · right
    refine ⟨by omega, ?_⟩
    exact Permutation_existsIndex xs' xs k av bv x Hperm.symm
      (fun i hi => (Hsame i hi).symm) ⟨by omega, by rw [← Hperm.length_eq]; exact Hb⟩ Hk

theorem close_segment (xs xs' : List E) (a b a_val b_val : Nat) :
    OutsideSame xs xs' a_val b_val →
    xs ≡ₚ xs' →
    IsPartiallySortedSeg R xs a b a_val b_val →
    IsSortedSeg R xs' a_val b_val →
    a_val ≤ b_val ∧ a ≤ a_val ∧ b ≥ b_val ∧ b ≤ xs.length →
    IsSortedSeg R xs' a b := by
  intro Hsame Hperm Hold Hnew Hb i j xi xj Hij Hi Hj
  by_cases hin : a_val ≤ i ∧ j < b_val
  · exact Hnew i j xi xj ⟨⟨hin.1, Hij.1.2⟩, hin.2⟩ Hi Hj
  rcases outsideSame_lookup xs xs' a_val b_val i xi Hsame Hperm (by omega) Hi with
    ⟨hi, Hi'⟩ | ⟨hi, i0, Hi0, hi0⟩ <;>
  rcases outsideSame_lookup xs xs' a_val b_val j xj Hsame Hperm (by omega) Hj with
    ⟨hj, Hj'⟩ | ⟨hj, j0, Hj0, hj0⟩
  · exact Hold i j xi xj Hij (by omega) Hi' Hj'
  · exact Hold i j0 xi xj ⟨⟨Hij.1.1, by omega⟩, by omega⟩ (by omega) Hi' Hj0
  · exact Hold i0 j xi xj ⟨⟨by omega, by omega⟩, Hij.2⟩ (by omega) Hi0 Hj'
  · omega

theorem isPartiallySortedSeg_perserve (xs xs' : List E) (a b a_val b_val : Nat) :
    IsPartiallySortedSeg R xs a b a_val b_val →
    xs ≡ₚ xs' →
    OutsideSame xs xs' a_val b_val →
    b_val ≤ xs.length ∧ a ≤ a_val ∧ b ≥ b_val →
    IsPartiallySortedSeg R xs' a b a_val b_val := by
  intro Hold Hperm Hsame Hb i j xi xj Hij Hout Hi Hj
  rcases outsideSame_lookup xs xs' a_val b_val i xi Hsame Hperm Hb.1 Hi with
    ⟨hi, Hi'⟩ | ⟨hi, i0, Hi0, hi0⟩ <;>
  rcases outsideSame_lookup xs xs' a_val b_val j xj Hsame Hperm Hb.1 Hj with
    ⟨hj, Hj'⟩ | ⟨hj, j0, Hj0, hj0⟩
  · exact Hold i j xi xj Hij Hout Hi' Hj'
  · exact Hold i j0 xi xj ⟨⟨Hij.1.1, by omega⟩, by omega⟩ (by omega) Hi' Hj0
  · exact Hold i0 j xi xj ⟨⟨by omega, by omega⟩, Hij.2⟩ (by omega) Hi0 Hj'
  · omega

/-- `IsPartitioned` is preserved by a permutation within `[l, r)` when `[l, r)`
lies on one side of the pivot `r0`. -/
theorem isPartitioned_preserve (xs2 xs3 : List E) (a_val b_val r0 l r : Nat)
    (Hperm : xs2 ≡ₚ xs3) (Hsame : OutsideSame xs2 xs3 l r) (Hr : r ≤ xs2.length)
    (Hpart : IsPartitioned R xs2 a_val b_val r0)
    (Hside : (a_val ≤ l ∧ r ≤ r0) ∨ (r0 < l ∧ r ≤ b_val)) :
    IsPartitioned R xs3 a_val b_val r0 := by
  intro i xr xi Hi Hr0
  have Hr0' : xs2[r0]? = some xr := (Hsame r0 (by omega)).trans Hr0
  rcases outsideSame_lookup xs2 xs3 l r i xi Hsame Hperm Hr Hi with
    ⟨_, Hi'⟩ | ⟨_, i0, Hi0, hi0⟩
  · exact Hpart i xr xi Hi' Hr0'
  · have H := Hpart i0 xr xi Hi0 Hr0'
    constructor
    · intro _; exact H.1 (by omega)
    · intro _; exact H.2 (by omega)

theorem restore_invariant1 [StrictWeakOrder R] (xs2 xs3 : List E) (a_val b_val a b r0 : Nat) :
    xs2 ≡ₚ xs3 →
    IsSortedSeg R xs3 a_val r0 →
    OutsideSame xs2 xs3 a_val r0 →
    IsPartiallySortedSeg R xs2 a b a_val b_val →
    IsPartitioned R xs2 a_val b_val r0 →
    (a ≤ a_val ∧ a_val ≤ r0) ∧ (r0 < b_val ∧ b_val ≤ b) ∧ b ≤ xs3.length →
    IsPartiallySortedSeg R xs3 a b (r0 + 1) b_val := by
  intro Hperm Hsorted Hsame Hps Hpart Hb
  have Hlen := Hperm.length_eq
  have Hps3 := isPartiallySortedSeg_perserve R xs2 xs3 a b a_val b_val Hps Hperm
    (outsideSame_loosen xs2 xs3 a_val r0 a_val b_val Hsame (by omega) (by omega))
    ⟨by omega, by omega, by omega⟩
  have Hpart3 := isPartitioned_preserve R xs2 xs3 a_val b_val r0 a_val r0 Hperm Hsame
    (by omega) Hpart (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)
  intro i j xi xj Hij Hout Hi Hj
  by_cases hia : i < a_val
  · exact Hps3 i j xi xj Hij (Or.inl hia) Hi Hj
  by_cases hjb : j ≥ b_val
  · exact Hps3 i j xi xj Hij (Or.inr hjb) Hi Hj
  have hir : i < r0 + 1 := by omega
  obtain ⟨xp, Hxp⟩ := lookup_lt_is_Some_2 (l := xs3) (i := r0) (by omega)
  by_cases hir0 : i = r0
  · subst hir0
    rw [Hi] at Hxp; cases Hxp
    exact (Hpart3 j xi xj Hj Hi).2 ⟨by omega, by omega⟩
  have Hpi : ¬ R xp xi := (Hpart3 i xp xi Hi Hxp).1 ⟨by omega, by omega⟩
  by_cases hjr : j ≥ r0
  · apply notR_trans R xi xp xj _ Hpi
    by_cases hjr0 : j = r0
    · subst hjr0; rw [Hj] at Hxp; cases Hxp; exact notR_refl R _
    · exact (Hpart3 j xp xj Hj Hxp).2 ⟨by omega, by omega⟩
  · exact Hsorted i j xi xj ⟨⟨by omega, Hij.1.2⟩, by omega⟩ Hi Hj

theorem restore_invariant2 [StrictWeakOrder R] (xs2 xs3 : List E) (a_val b_val a b r0 : Nat) :
    xs2 ≡ₚ xs3 →
    IsSortedSeg R xs3 (r0 + 1) b_val →
    OutsideSame xs2 xs3 (r0 + 1) b_val →
    IsPartiallySortedSeg R xs2 a b a_val b_val →
    IsPartitioned R xs2 a_val b_val r0 →
    (a ≤ a_val ∧ a_val ≤ r0) ∧ (r0 < b_val ∧ b_val ≤ b) ∧ b ≤ xs3.length →
    IsPartiallySortedSeg R xs3 a b a_val r0 := by
  intro Hperm Hsorted Hsame Hps Hpart Hb
  have Hlen := Hperm.length_eq
  have Hps3 := isPartiallySortedSeg_perserve R xs2 xs3 a b a_val b_val Hps Hperm
    (outsideSame_loosen xs2 xs3 (r0 + 1) b_val a_val b_val Hsame (by omega) (by omega))
    ⟨by omega, by omega, by omega⟩
  have Hpart3 := isPartitioned_preserve R xs2 xs3 a_val b_val r0 (r0 + 1) b_val Hperm Hsame
    (by omega) Hpart (Or.inr ⟨by omega, Nat.le_refl _⟩)
  intro i j xi xj Hij Hout Hi Hj
  by_cases hia : i < a_val
  · exact Hps3 i j xi xj Hij (Or.inl hia) Hi Hj
  by_cases hjb : j ≥ b_val
  · exact Hps3 i j xi xj Hij (Or.inr hjb) Hi Hj
  have hjr : j ≥ r0 := by omega
  obtain ⟨xp, Hxp⟩ := lookup_lt_is_Some_2 (l := xs3) (i := r0) (by omega)
  by_cases hjr0 : j = r0
  · subst hjr0
    rw [Hj] at Hxp; cases Hxp
    exact (Hpart3 i xj xi Hi Hj).1 ⟨by omega, by omega⟩
  have Hjp : ¬ R xj xp := (Hpart3 j xp xj Hj Hxp).2 ⟨by omega, by omega⟩
  by_cases hir : i ≤ r0
  · apply notR_trans R xi xp xj Hjp
    by_cases hir0 : i = r0
    · subst hir0; rw [Hi] at Hxp; cases Hxp; exact notR_refl R _
    · exact (Hpart3 i xp xi Hi Hxp).1 ⟨by omega, by omega⟩
  · exact Hsorted i j xi xj ⟨⟨by omega, Hij.1.2⟩, by omega⟩ Hi Hj

theorem partition_header (xs : List E) (a b r : Nat) :
    IsPartitioned R xs a b r → header R xs (r + 1) b := by
  intro H
  unfold header OneLeSeg
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  intro xi j xj Hj Hxi Hxj
  exact (H j xi xj Hxj Hxi).2 ⟨by omega, Hj.2⟩

end pure

section hide
variable {GF : BundledGFunctors}

/-- `P` under an opaque name, to keep the Löb induction hypothesis of
`wp_pdqsortCmpFunc` (which contains `▷`s) away from the later stripping that the
proof mode does for every hypothesis mentioning `▷` at every symbolic execution
step. -/
def pdqHide (P : IProp GF) : IProp GF := P

theorem pdqHide_intro {P Q : IProp GF} : (□ pdqHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

theorem pdqHide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ pdqHide P -∗ Q) := .rfl

end hide

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

/-- Unfold `cmpImplements` into the Texan triple for `cmp_code` (so that it
can be `wp_apply`ed without unfolding `cmpImplements` in the goal). -/
theorem cmpImplements_elim (cmp_code : GoFunc) :
    cmpImplements (GF := GF) R cmp_code ⊢ iprop(∀ (x y : E),
      {{ True }}
        (App (App (Val #cmp_code) (Val #x)) (Val #y))
      {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }}) := by
  unfold cmpImplements; exact .rfl

theorem wp_reverseRangeCmpFunc (data : GoSlice) (a b : w64) (cmp_code : GoFunc) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (App (Val #(functions reverseRangeCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave HI : (∃ (xs1 : List E) (i_val j_val : w64),
      "Hxs" ∷ data ↦* xs1 ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "%ij_bound" ∷ ⌜sint.Z a ≤ sint.Z i_val ∧ sint.Z j_val < sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [Hxs i j]
  · iexists xs, _, _
    iframe
    ipureintro
    exact ⟨by word, List.Perm.refl _, outsideSame_refl _ _ _⟩
  wp_for HI
  wp_if_destruct
  · have Hl := HPerm1.length_eq
    ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
    list_elem xs1 (sint.nat j_val) as xj
    list_elem xs1 (sint.nat i_val) as xi
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxj_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxi_lookup
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z i_val) xs1 xj $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; constructor <;> word
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z j_val) _ xi $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp only [List.length_set]; constructor <;> word
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_⟩
    · exact HPerm1.trans (swap_perm xs1 (sint.nat j_val) (sint.nat i_val) xj xi
        Hxj_lookup Hxi_lookup)
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, Houtside1⟩

theorem wp_pdqsortCmpFunc (data : GoSlice) (a b limit : w64) (cmp_code : GoFunc) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "%Header" ∷ ⌜header R xs (sint.nat a) (sint.nat b)⌝ ∗
        "#Hcmp" ∷ cmpImplements R cmp_code }}
      (App (App (App (App (App (Val #(functions pdqsortCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #limit)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat b)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  iloeb as IH generalizing %data %a %b %limit %xs
  irevert IH
  iapply pdqHide_intro
  iintro #IH
  wp_start as H
  iNamed H
  wp_auto
  -- loop invariant for the outer loop
  ihave HI : (∃ (a_val b_val limit : w64) (bl1 bl2 : Bool) (xs' : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "limit" ∷ limit_ptr ↦ limit ∗
      "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗
      "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%ab_range" ∷ ⌜sint.Z a ≤ sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧
        sint.Z b_val ≤ sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Header" ∷ ⌜header R xs' (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%HPartialsorted" ∷ ⌜IsPartiallySortedSeg R xs' (sint.nat a) (sint.nat b)
        (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF)
      $$ [a b limit Hxs wasPartitioned wasBalanced]
  · iexists a, b, limit, true, true, xs
    iframe
    ipureintro
    refine ⟨by omega, List.Perm.refl _, Header, ?_, outsideSame_refl _ _ _⟩
    intro i j xi xj Hij Hout; omega
  wp_for HI
  have Hlen_x' := HPerm1.length_eq
  wp_if_destruct
  · -- falls to insertionSort
    wp_apply wp_insertionSortCmpFunc R data a_val b_val cmp_code xs' $$ [Hxs]
      with %xs'' ⟨Hxs, %Hperm1, %Hsorted, %Houtside⟩
    · iframe Hxs; iframe #; ipureintro; word
    wp_for_post
    iapply HΦ
    iframe Hxs
    ipureintro
    refine ⟨HPerm1.trans Hperm1, ?_, ?_⟩
    · exact close_segment R xs' xs'' _ _ _ _ Houtside Hperm1 HPartialsorted Hsorted (by word)
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_loosen _ _ _ _ _ _ Houtside (by word) (by word))
  wp_if_destruct
  · -- falls to heapSort
    wp_apply wp_heapSortCmpFunc R data a_val b_val cmp_code xs' $$ [Hxs]
      with %xs'' ⟨Hxs, %Hperm1, %Hsorted, %Houtside⟩
    · iframe Hxs; iframe #; ipureintro; word
    wp_for_post
    iapply HΦ
    iframe Hxs
    ipureintro
    refine ⟨HPerm1.trans Hperm1, ?_, ?_⟩
    · exact close_segment R xs' xs'' _ _ _ _ Houtside Hperm1 HPartialsorted Hsorted (by word)
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_loosen _ _ _ _ _ _ Houtside (by word) (by word))
  -- pattern breaking
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (limit : w64) (xs' : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "cmp" ∷ cmp_ptr ↦ cmp_code ∗
      "data" ∷ data_ptr ↦ data ∗
      "limit" ∷ limit_ptr ↦ limit ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%HPerm2" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%HPartialsorted2" ∷ ⌜IsPartiallySortedSeg R xs' (sint.nat a) (sint.nat b)
        (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Header2" ∷ ⌜header R xs' (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Houtside2" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝))) $$ [a b cmp data limit Hxs]
  · cases bl2
    · simp only [Bool.not_false]
      wp_auto
      wp_apply wp_breakPatternsCmpFunc R data a_val b_val cmp_code xs' $$ [Hxs]
        with %xs2 ⟨Hxs, %Hperm2, %Houtside2⟩
      · iframe Hxs; iframe #; ipureintro; word
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, xs2
      iframe
      ipureintro
      refine ⟨HPerm1.trans Hperm2, ?_, ?_, ?_⟩
      · exact isPartiallySortedSeg_perserve R _ _ _ _ _ _ HPartialsorted Hperm2 Houtside2
          (by word)
      · exact header_preserve R _ _ _ _ Header Hperm2 Houtside2 (by word)
      · exact outsideSame_trans _ _ _ _ _ Houtside1
          (outsideSame_loosen _ _ _ _ _ _ Houtside2 (by word) (by word))
    · simp only [Bool.not_true]
      wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, xs'
      iframe
      ipureintro
      exact ⟨HPerm1, HPartialsorted, Header, Houtside1⟩
  iintro %v ⟨%Hv, %limit1, %xs2, Hpost⟩
  subst Hv
  iNamed Hpost
  clear HPerm1 HPartialsorted Header Houtside1 Hlen_x'
  have Hlen2 := HPerm2.length_eq
  wp_auto
  wp_apply wp_choosePivotCmpFunc R data a_val b_val cmp_code xs2 $$ [Hxs]
    with %r %hint ⟨Hxs, %Hrbound⟩
  · iframe Hxs; iframe #; ipureintro; word
  -- reverse a decreasing range
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (xs' : List E) (hint : slices.sortedHint) (r : w64),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "cmp" ∷ cmp_ptr ↦ cmp_code ∗
      "data" ∷ data_ptr ↦ data ∗
      "hint" ∷ hint_ptr ↦ hint ∗
      "pivot" ∷ pivot_ptr ↦ r ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%HPerm3" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%HPartialsorted3" ∷ ⌜IsPartiallySortedSeg R xs' (sint.nat a) (sint.nat b)
        (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Houtside3" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ ∗
      "%Header3" ∷ ⌜header R xs' (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%rrange" ∷ ⌜sint.Z a_val ≤ sint.Z r ∧ sint.Z r < sint.Z b_val⌝)))
      $$ [a b cmp data hint pivot Hxs]
  · try simp only [decreasingHint, increasingHint]
    wp_pures
    wp_if_destruct
    · wp_apply wp_reverseRangeCmpFunc R data a_val b_val cmp_code xs2 $$ [Hxs]
        with %xs3 ⟨Hxs, %Hperm, %Houtside⟩
      · iframe Hxs; iframe #; ipureintro; word
      isplitr
      · ipureintro; first | rfl | trivial
      iexists xs3, _, _
      iframe
      ipureintro
      refine ⟨HPerm2.trans Hperm, ?_, ?_, ?_, by word⟩
      · exact isPartiallySortedSeg_perserve R _ _ _ _ _ _ HPartialsorted2 Hperm Houtside
          (by word)
      · exact outsideSame_trans _ _ _ _ _ Houtside2
          (outsideSame_loosen _ _ _ _ _ _ Houtside (by word) (by word))
      · exact header_preserve R _ _ _ _ Header2 Hperm Houtside (by word)
    · isplitr
      · ipureintro; first | rfl | trivial
      iexists xs2, _, _
      iframe
      ipureintro
      exact ⟨HPerm2, HPartialsorted2, Houtside2, Header2, Hrbound⟩
  iintro %v ⟨%Hv, %xs3, %hint3, %r3, Hpost⟩
  subst Hv
  iNamed Hpost
  clear HPerm2 HPartialsorted2 Header2 Houtside2 Hlen2 Hrbound
  have Hlen3 := HPerm3.length_eq
  wp_auto
  -- partial insertion sort if the slice looks sorted
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(∃ (xs4 : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "cmp" ∷ cmp_ptr ↦ cmp_code ∗
      "data" ∷ data_ptr ↦ data ∗
      "hint" ∷ hint_ptr ↦ hint3 ∗
      "pivot" ∷ pivot_ptr ↦ r3 ∗
      "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗
      "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗
      "Hxs" ∷ data ↦* xs4 ∗
      "%HPerm4" ∷ ⌜xs3 ≡ₚ xs4⌝ ∗
      "%Houtside4" ∷ ⌜OutsideSame xs3 xs4 (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Header4" ∷ ⌜header R xs4 (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Hpost4" ∷ ⌜(v = returnVal #() ∧ IsSortedSeg R xs4 (sint.nat a) (sint.nat b)) ∨
        v = executeVal⌝)))
      $$ [a b cmp data hint pivot Hxs wasPartitioned wasBalanced]
  · try simp only [increasingHint]
    cases bl2
    · wp_auto
      iexists xs3; iframe; ipureintro
      refine ⟨List.Perm.refl _, outsideSame_refl _ _ _, Header3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
    cases bl1
    · wp_auto
      iexists xs3; iframe; ipureintro
      refine ⟨List.Perm.refl _, outsideSame_refl _ _ _, Header3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
    wp_auto
    wp_if_destruct
    · wp_apply wp_partialInsertionSortCmpFunc R data a_val b_val cmp_code xs3 $$ [Hxs]
        with %xs4 %bl ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
      · iframe Hxs; iframe #; ipureintro; exact ⟨Header3, by word⟩
      cases bl
      · wp_auto
        iexists xs4; iframe; ipureintro
        refine ⟨Hperm, Houtside, header_preserve R _ _ _ _ Header3 Hperm Houtside (by word), ?_⟩
        first | exact Or.inr rfl | trivial | simp
      · wp_auto
        iexists xs4; iframe; ipureintro
        refine ⟨Hperm, Houtside, header_preserve R _ _ _ _ Header3 Hperm Houtside (by word), ?_⟩
        left
        refine ⟨rfl, ?_⟩
        exact close_segment R xs3 xs4 _ _ _ _ Houtside Hperm HPartialsorted3 Hsorted (by word)
    · iexists xs3; iframe; ipureintro
      refine ⟨List.Perm.refl _, outsideSame_refl _ _ _, Header3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
  iintro %v ⟨%xs4, Hpost⟩
  iNamed Hpost
  rcases Hpost4 with ⟨Hv, Hsorted4⟩ | Hv
  · subst Hv
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hxs
    ipureintro
    refine ⟨HPerm3.trans HPerm4, Hsorted4, ?_⟩
    exact outsideSame_trans _ _ _ _ _ Houtside3
      (outsideSame_loosen _ _ _ _ _ _ Houtside4 (by word) (by word))
  subst Hv
  have HPartialsorted4 := isPartiallySortedSeg_perserve R _ _ _ _ _ _ HPartialsorted3 HPerm4
    Houtside4 (by word)
  have HPerm4' := HPerm3.trans HPerm4
  have Houtside4' := outsideSame_trans _ _ _ _ _ Houtside3
    (outsideSame_loosen _ _ _ _ _ _ Houtside4 (by word) (by word))
  have Hlen4 := HPerm4'.length_eq
  clear HPerm3 HPartialsorted3 Header3 Houtside3 Hlen3 HPerm4 Houtside4
  wp_auto
  -- the pivot is the minimum of the segment: partition equal elements
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(∃ (xs5 : List E) (new_a : w64),
      "a" ∷ a_ptr ↦ new_a ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "cmp" ∷ cmp_ptr ↦ cmp_code ∗
      "data" ∷ data_ptr ↦ data ∗
      "pivot" ∷ pivot_ptr ↦ r3 ∗
      "Hxs" ∷ data ↦* xs5 ∗
      "%ab_range5" ∷ ⌜sint.Z a ≤ sint.Z new_a ∧ sint.Z new_a ≤ sint.Z b_val ∧
        sint.Z b_val ≤ sint.Z b⌝ ∗
      "%HPerm5" ∷ ⌜xs ≡ₚ xs5⌝ ∗
      "%Houtside5" ∷ ⌜OutsideSame xs4 xs5 (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Header5" ∷ ⌜header R xs5 (sint.nat a_val) (sint.nat b_val)⌝ ∗
      "%Hpost5" ∷ ⌜(v = continueVal ∧ sint.Z new_a > sint.Z a_val ∧
          IsEqPartitioned R xs5 (sint.nat a_val) (sint.nat b_val) (sint.nat new_a)) ∨
        (v = executeVal ∧ xs5 = xs4 ∧ new_a = a_val)⌝)))
      $$ [a b cmp data pivot Hxs]
  · wp_if_destruct
    · ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
      list_elem xs4 (sint.nat (a_val - W64 1)) as xa
      list_elem xs4 (sint.nat r3) as xr
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z (a_val - W64 1)) xs4 _ xa (by word) $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; exact Hxa_lookup
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z r3) xs4 _ xr (by word) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxr_lookup
      ihave #Hcmp' := cmpImplements_elim R cmp_code $$ Hcmp
      wp_apply Hcmp' with %c %Hc
      iclear Hcmp'
      wp_if_destruct
      · iexists xs4, a_val
        iframe
        ipureintro
        refine ⟨by word, HPerm4', outsideSame_refl _ _ _, Header4, ?_⟩
        first | exact Or.inr ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨trivial, rfl, rfl⟩
      · wp_apply wp_partitionEqualCmpFunc R data a_val b_val r3 cmp_code xs4 $$ [Hxs]
          with %xs5 %new_a ⟨Hxs, %Hrange5, %Hperm5, %Hpart5, %Houtside5⟩
        · iframe Hxs; iframe #; ipureintro
          refine ⟨by word, by word, ?_⟩
          intro xi j xj Hj Hxi Hxj
          rw [Hxr_lookup] at Hxi; cases Hxi
          have Hnr : ¬ R xa xr := fun h => Hif (by have := Hc.2 h; word)
          have H4 := Header4
          unfold header at H4
          rw [if_neg (by word)] at H4
          have Hxa' : xs4[sint.nat a_val - 1]? = some xa := by
            rw [show sint.nat a_val - 1 = sint.nat (a_val - W64 1) by word]; exact Hxa_lookup
          exact notR_trans R xr xa xj (H4 xa j xj Hj Hxa' Hxj) Hnr
        iexists xs5, new_a
        iframe
        ipureintro
        refine ⟨by word, HPerm4'.trans Hperm5, Houtside5,
          header_preserve R _ _ _ _ Header4 Hperm5 Houtside5 (by word), ?_⟩
        left
        exact ⟨rfl, by word, Hpart5⟩
    · iexists xs4, a_val
      iframe
      ipureintro
      refine ⟨by word, HPerm4', outsideSame_refl _ _ _, Header4, ?_⟩
      first | exact Or.inr ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨trivial, rfl, rfl⟩
  iintro %v ⟨%xs5, %new_a, Hpost⟩
  iNamed Hpost
  rcases Hpost5 with ⟨Hv, Hnew_a, Hpart5⟩ | ⟨Hv, Hxs5, Hnew_a⟩
  · -- `continue` after partitioning out the elements equal to the pivot
    subst Hv
    have Hperm45 : xs4 ≡ₚ xs5 := HPerm4'.symm.trans HPerm5
    have Hps5 := isPartiallySortedSeg_perserve R _ _ _ _ _ _ HPartialsorted4 Hperm45
      Houtside5 (by word)
    wp_auto
    wp_for_post
    iframe
    iexists new_a, b_val, limit1, bl1, bl2, xs5
    iframe
    ipureintro
    refine ⟨by word, HPerm5, ?_, ?_, ?_⟩
    · unfold header OneLeSeg
      rw [if_neg (by word)]
      intro xi j xj Hj Hxi Hxj
      exact Hpart5 (sint.nat new_a - 1) j xi xj Hxi Hxj ⟨by word, ⟨by word, Hj.2⟩, by word⟩
    · intro i j xi xj Hij Hout Hxi Hxj
      by_cases hia : i < sint.nat a_val
      · exact Hps5 i j xi xj Hij (Or.inl hia) Hxi Hxj
      by_cases hjb : j ≥ sint.nat b_val
      · exact Hps5 i j xi xj Hij (Or.inr hjb) Hxi Hxj
      exact Hpart5 i j xi xj Hxi Hxj ⟨by omega, ⟨Hij.1.2, by omega⟩, by omega⟩
    · exact outsideSame_trans _ _ _ _ _ Houtside4'
        (outsideSame_loosen _ _ _ _ _ _ Houtside5 (by word) (by word))
  subst Hv
  subst xs5
  subst new_a
  clear Houtside5 HPerm5 Header5 ab_range5
  wp_auto
  wp_apply wp_partitionCmpFunc R data a_val b_val r3 cmp_code xs4 $$ [Hxs]
    with %xs6 %bl %r1 ⟨Hxs, %rrange1, %Hperm6, %Hpart6, %Houtside6⟩
  · iframe Hxs; iframe #; ipureintro; exact ⟨by word, by word⟩
  have HPerm6' := HPerm4'.trans Hperm6
  have Houtside6' := outsideSame_trans _ _ _ _ _ Houtside4'
    (outsideSame_loosen _ _ _ _ _ _ Houtside6 (by word) (by word))
  have HPartialsorted6 := isPartiallySortedSeg_perserve R _ _ _ _ _ _ HPartialsorted4 Hperm6
    Houtside6 (by word)
  have Header6 := header_preserve R _ _ _ _ Header4 Hperm6 Houtside6 (by word)
  have Hlen6 := HPerm6'.length_eq
  have Hr1 : sint.nat (r1 + W64 1) = sint.nat r1 + 1 := by word
  -- (unhidden before the pure steps of the `if`, which strip its `▷`)
  irevert IH
  iapply pdqHide_elim
  iintro #IH
  wp_if_destruct
  · -- recurse on the (smaller) left part
    rw [func_unfold]
    wp_apply IH $$ %data %a_val %r1 %limit1 %xs6 [Hxs] with %xs7 ⟨Hxs, %Hperm7, %Hsorted7, %Houtside7⟩
    · iframe Hxs; iframe #; ipureintro
      refine ⟨by word, ?_⟩
      unfold header at Header6 ⊢
      split
      · trivial
      · rename_i h; rw [if_neg h] at Header6
        intro xi j xj Hj Hxi Hxj
        exact Header6 xi j xj ⟨Hj.1, by word⟩ Hxi Hxj
    have Hl67 := Hperm7.length_eq
    wp_for_post
    iframe
    iexists (r1 + W64 1), b_val, limit1, bl, _, xs7
    iframe
    ipureintro
    rw [Hr1]
    refine ⟨by word, HPerm6'.trans Hperm7, ?_, ?_, ?_⟩
    · unfold header OneLeSeg
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      intro xi j xj Hj Hxi Hxj
      rw [← Houtside7 _ (by omega)] at Hxi Hxj
      exact (Hpart6 j xi xj Hxj Hxi).2 ⟨by omega, by omega⟩
    · exact restore_invariant1 R xs6 xs7 _ _ _ _ _ Hperm7 Hsorted7 Houtside7 HPartialsorted6
        Hpart6 (by word)
    · exact outsideSame_trans _ _ _ _ _ Houtside6'
        (outsideSame_loosen _ _ _ _ _ _ Houtside7 (by word) (by word))
  · -- recurse on the (smaller) right part
    rw [func_unfold]
    wp_apply IH $$ %data %(r1 + W64 1) %b_val %limit1 %xs6 [Hxs]
      with %xs7 ⟨Hxs, %Hperm7, %Hsorted7, %Houtside7⟩
    · iframe Hxs; iframe #; ipureintro
      refine ⟨by word, ?_⟩
      rw [Hr1]
      exact partition_header R _ _ _ _ Hpart6
    have Hl67 := Hperm7.length_eq
    rw [Hr1] at Hsorted7 Houtside7
    wp_for_post
    iframe
    iexists a_val, r1, limit1, bl, _, xs7
    iframe
    ipureintro
    refine ⟨by word, HPerm6'.trans Hperm7, ?_, ?_, ?_⟩
    · unfold header at Header6 ⊢
      split
      · trivial
      · rename_i h; rw [if_neg h] at Header6
        intro xi j xj Hj Hxi Hxj
        rw [← Houtside7 _ (by omega)] at Hxi Hxj
        exact Header6 xi j xj ⟨Hj.1, by word⟩ Hxi Hxj
    · exact restore_invariant2 R xs6 xs7 _ _ _ _ _ Hperm7 Hsorted7 Houtside7 HPartialsorted6
        Hpart6 (by word)
    · exact outsideSame_trans _ _ _ _ _ Houtside6'
        (outsideSame_loosen _ _ _ _ _ _ Houtside7 (by word) (by word))

end proof

end slices

end Perennial
end
