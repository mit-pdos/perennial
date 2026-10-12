/-
The pure facts of the proof of `pdqsortCmpFunc` (reused by `pdqsortOrdered`), `pdqHide`
and `cmpImplements_elim`.
-/
module

public import Perennial.Proof.slices.SortBasics
public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Proof.slices.InsertionSortBasics
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

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

end proof

end slices

end Perennial
end
