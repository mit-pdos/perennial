/-
The pure facts and the loop lemmas of the proofs of `insertionSortCmpFunc` and
`partialInsertionSortCmpFunc`.
-/
module

public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

/-! ### Pure facts for the insertion sort loops -/

section pure
variable {E : Type} (R : E → E → Prop)

/-- Inner-loop invariant of insertion sort: `xs[a..i]` is sorted except for
pairs whose larger index is the hole `j`. -/
def InsBr (xs : List E) (a i j : Nat) : Prop :=
  ∀ (i' j' : Nat) xi xj, (a ≤ i' ∧ i' < j') ∧ j' ≤ i → j' ≠ j →
    xs[i']? = some xi → xs[j']? = some xj → ¬ R xj xi

theorem insBr_init (xs : List E) (a i : Nat) :
    IsSortedSeg R xs a i → InsBr R xs a i i := by
  intro H i' j' xi xj hb hne hi hj
  exact H i' j' xi xj ⟨hb.1, by omega⟩ hi hj

theorem isSortedSeg_mono (xs : List E) (a i b : Nat) (h : b ≤ i) :
    IsSortedSeg R xs a i → IsSortedSeg R xs a b := by
  intro H i' j' xi xj hb hi hj
  exact H i' j' xi xj ⟨hb.1, by omega⟩ hi hj

theorem isSortedSeg_one (xs : List E) (a : Nat) : IsSortedSeg R xs a (a + 1) := by
  intro i' j' xi xj hb; omega

theorem insBr_swap [StrictWeakOrder R] (xs : List E) (a i j : Nat) (x0 x1 : E)
    (H : InsBr R xs a i j) (haj : a < j) (hji : j ≤ i)
    (h0 : xs[j]? = some x0) (h1 : xs[j - 1]? = some x1) (hR : R x0 x1) :
    InsBr R ((xs.set j x1).set (j - 1) x0) a i (j - 1) := by
  have hj := lookup_lt_Some h0
  have hy1 : ((xs.set j x1).set (j - 1) x0)[j - 1]? = some x0 := by
    rw [List.getElem?_set_self (by simp; omega)]
  have hy2 : ((xs.set j x1).set (j - 1) x0)[j]? = some x1 := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  have hy3 : ∀ k, k ≠ j - 1 → k ≠ j → ((xs.set j x1).set (j - 1) x0)[k]? = xs[k]? := by
    intro k hk1 hk2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  intro i' j' xi xj hb hne hi hj'
  by_cases hjj : j' = j
  · subst hjj
    rw [hy2] at hj'; cases hj'
    by_cases hii : i' = j' - 1
    · subst hii; rw [hy1] at hi; cases hi
      exact R_antisym R _ _ hR
    · rw [hy3 _ hii (by omega)] at hi
      exact H i' (j' - 1) xi _ ⟨⟨hb.1.1, by omega⟩, by omega⟩ (by omega) hi h1
  · rw [hy3 _ hne hjj] at hj'
    by_cases hii : i' = j - 1
    · subst hii; rw [hy1] at hi; cases hi
      exact H j j' x0 xj ⟨⟨by omega, by omega⟩, hb.2⟩ hjj h0 hj'
    by_cases hii2 : i' = j
    · subst hii2; rw [hy2] at hi; cases hi
      exact H (i' - 1) j' x1 xj ⟨⟨by omega, by omega⟩, hb.2⟩ hjj h1 hj'
    · rw [hy3 _ hii hii2] at hi
      exact H i' j' xi xj hb hjj hi hj'

theorem insBr_done_a (xs : List E) (a i j : Nat) (H : InsBr R xs a i j) (hj : j = a) :
    IsSortedSeg R xs a (i + 1) := by
  intro i' j' xi xj hb hi hj'
  exact H i' j' xi xj ⟨hb.1, by omega⟩ (by omega) hi hj'

theorem insBr_done_cmp [StrictWeakOrder R] (xs : List E) (a i j : Nat) (x0 x1 : E)
    (H : InsBr R xs a i j) (haj : a < j) (hji : j ≤ i)
    (h0 : xs[j]? = some x0) (h1 : xs[j - 1]? = some x1) (hR : ¬ R x0 x1) :
    IsSortedSeg R xs a (i + 1) := by
  intro i' j' xi xj hb hi hj'
  by_cases hjj : j' = j
  · subst hjj
    rw [h0] at hj'; cases hj'
    by_cases hii : i' = j' - 1
    · subst hii; rw [h1] at hi; cases hi; exact hR
    · have := H i' (j' - 1) xi x1 ⟨⟨hb.1.1, by omega⟩, by omega⟩ (by omega) hi h1
      exact notR_trans R xi x1 x0 hR this
  · exact H i' j' xi xj ⟨hb.1, by omega⟩ hjj hi hj'

theorem isSortedSeg_swap_hi (xs : List E) (a i k1 k2 : Nat) (v1 v2 : E)
    (H : IsSortedSeg R xs a i) (h1 : i ≤ k1) (h2 : i ≤ k2) :
    IsSortedSeg R ((xs.set k1 v1).set k2 v2) a i := by
  intro i' j' xi xj hb hi hj
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at hi hj
  exact H i' j' xi xj hb hi hj

theorem isSortedSeg_scan [StrictWeakOrder R] (xs : List E) (a i : Nat) (x0 x1 : E)
    (H : IsSortedSeg R xs a i) (hai : a < i)
    (h0 : xs[i]? = some x0) (h1 : xs[i - 1]? = some x1) (hR : ¬ R x0 x1) :
    IsSortedSeg R xs a (i + 1) :=
  insBr_done_cmp R xs a i i x0 x1 (insBr_init R xs a i H) hai (Nat.le_refl _) h0 h1 hR

theorem header_contra (xs : List E) (a b : Nat) (x0 x1 : E)
    (H : header R xs a b) (ha : 0 < a) (hab : a < b)
    (h0 : xs[a]? = some x0) (h1 : xs[a - 1]? = some x1) : ¬ R x0 x1 := by
  unfold header at H
  simp only [show a ≠ 0 by omega, ↓reduceIte] at H
  exact H x1 a x0 ⟨Nat.le_refl _, hab⟩ h1 h0

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

omit [ZeroVal E] [TypedPointsto (GF := GF) E] [IntoValTyped (GF := GF) E Et] [StrictWeakOrder R]
  package_sem sem in
/-- A call of the comparison function, with `cmpImplements` kept folded in the
caller's context: unfolded, its `▷` makes every symbolic execution step search
for laters to strip in all hypotheses. -/
theorem ins_wp_cmp (cmp_code : GoFunc) (x y : E) :
    {{ cmpImplements (GF := GF) R cmp_code }}
      (App (App (Val #cmp_code) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }} := by
  iintro %Φ #Hc HΦ
  unfold cmpImplements
  iapply Hc $$ [] HΦ
  itrivial

omit package_sem in
/-- The inner loop of `insertionSortCmpFunc` (a separate theorem, so that it
elaborates in parallel). -/
theorem ins_wp_insertion_inner (data : GoSlice) (a b i_val : w64) (cmp : GoFunc)
    (xs : List E) (cmp_ptr a_ptr data_ptr j_ptr : Loc) (Φ : val → IProp GF)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len)
    (irange : sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ max (sint.Z a + 1) (sint.Z b))
    (Hif : sint.Z i_val < sint.Z b) :
    ⊢ cmpImplements R cmp -∗ cmp_ptr ↦ cmp -∗ a_ptr ↦ a -∗ data_ptr ↦ data -∗
      (∃ (j_val : w64) (xs'' : List E),
        "j" ∷ j_ptr ↦ j_val ∗
        "Hxs" ∷ data ↦* xs'' ∗
        "%jrange" ∷ ⌜sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z i_val⌝ ∗
        "%Hperm2" ∷ ⌜xs ≡ₚ xs''⌝ ∗
        "%HsortedBr" ∷ ⌜InsBr R xs'' (sint.nat a) (sint.nat i_val) (sint.nat j_val)⌝ ∗
        "%Houtside2" ∷ ⌜OutsideSame xs xs'' (sint.nat a) (sint.nat b)⌝ : IProp GF) -∗
      (∀ xs'' : List E, data ↦* xs'' ∗ cmp_ptr ↦ cmp ∗ a_ptr ↦ a ∗ data_ptr ↦ data ∗
        ⌜xs ≡ₚ xs'' ∧ IsSortedSeg R xs'' (sint.nat a) (sint.nat i_val + 1) ∧
          OutsideSame xs xs'' (sint.nat a) (sint.nat b)⌝ -∗ Φ executeVal) -∗
      WP (((doFor
          glv(λ: <>,
              if: ![go.int] #j_ptr >⟨go.int⟩ ![go.int] #a_ptr then
                (let: "$a0" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                    let: "$a1" :=
                      ![Et]
                        ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
                      (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0") "$a1") <⟨go.int⟩
                  #(W64 0) else
                #false))
        glv(λ: <>,
            let: "$r0" :=
              ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
              let: "$r1" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                do: (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr) <-[Et] "$r0" ;;;
                  do:
                    (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1)) <-[Et]
                      "$r1"))
      glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) {{ Φ }} := by
  iintro #Hcmp cmp a data HI2 HΦ
  wp_for HI2
  have hlen'' := Hperm2.length_eq
  wp_if_destruct
  · list_elem xs'' (sint.nat j_val) as x0
    list_elem xs'' (sint.nat (j_val - W64 1)) as x1
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z j_val) xs'' _ x0 (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hx0_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z (j_val - W64 1)) xs'' _ x1 (by word) $$ [Hxs]
      with Hxs
    · iframe Hxs; ipureintro; exact Hx1_lookup
    wp_apply ins_wp_cmp R cmp $$ Hcmp with %r %Hr
    cleanup_bool_decide
    by_cases hc : sint.Z r < sint.Z (W64 0)
    · simp only [hc, _root_.decide_true, ↓reduceIte]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z (j_val - W64 1)) xs'' _ x1 (by word) $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; exact Hx1_lookup
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z j_val) xs'' _ x0 (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hx0_lookup
      slice_index_if
      wp_pures
      wp_apply wp_store_slice_index data (sint.Z j_val) xs'' x1 $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; omega
      slice_index_if
      wp_pures
      wp_apply wp_store_slice_index data (sint.Z (j_val - W64 1)) _ x0 $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; simp only [List.length_set]; word
      wp_for_post
      iframe
      iexists (j_val - W64 1), _
      iframe
      ipureintro
      have hj1 : sint.nat (j_val - W64 1) = sint.nat j_val - 1 := by word
      rw [show (sint.Z (j_val - W64 1)).toNat = sint.nat j_val - 1 from hj1,
        show (sint.Z j_val).toNat = sint.nat j_val from rfl]
      rw [hj1] at Hx1_lookup ⊢
      have hR := Hr.1 (by word)
      refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
      · exact Hperm2.trans (swap_perm _ _ _ _ _ Hx1_lookup Hx0_lookup)
      · exact insBr_swap R _ _ _ _ _ _ HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
      · exact outsideSame_trans _ _ _ _ _ Houtside2
          (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      iapply HΦ
      iframe
      ipureintro
      have hj1 : sint.nat (j_val - W64 1) = sint.nat j_val - 1 := by word
      rw [hj1] at Hx1_lookup
      have hR : ¬ R x0 x1 := fun h => hc (Hr.2 h)
      refine ⟨Hperm2, ?_, Houtside2⟩
      exact insBr_done_cmp R _ _ _ _ _ _ HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
  · iapply HΦ
    iframe
    ipureintro
    refine ⟨Hperm2, ?_, Houtside2⟩
    exact insBr_done_a R _ _ _ _ HsortedBr (by word)

omit package_sem in
/-- The loop of `partialInsertionSortCmpFunc` that shifts the smaller element
`data[i-1]` to the left (a separate theorem, so that it elaborates in parallel). -/
theorem ins_wp_shift_left (data : GoSlice) (a b i_val : w64) (cmp_code : GoFunc)
    (xs : List E) (cmp_ptr a_ptr data_ptr i_ptr j_ptr : Loc)
    (Header : header R xs (sint.nat a) (sint.nat b))
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len)
    (irange : sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b)
    (Hib : sint.Z i_val < sint.Z b) :
    ⊢ cmpImplements R cmp_code -∗ cmp_ptr ↦ cmp_code -∗ a_ptr ↦ a -∗ data_ptr ↦ data -∗
      i_ptr ↦ i_val -∗
      (∃ (jl : w64) (xs3 : List E),
        "jl" ∷ j_ptr ↦ jl ∗
        "Hxs" ∷ data ↦* xs3 ∗
        "%jrange" ∷ ⌜sint.Z a ≤ sint.Z jl ∧ sint.Z jl ≤ sint.Z i_val - 1⌝ ∗
        "%Hperm3" ∷ ⌜xs ≡ₚ xs3⌝ ∗
        "%HsortedBr" ∷ ⌜InsBr R xs3 (sint.nat a) (sint.nat i_val - 1) (sint.nat jl)⌝ ∗
        "%Houtside3" ∷ ⌜OutsideSame xs xs3 (sint.nat a) (sint.nat b)⌝ : IProp GF) -∗
      WP (((doFor glv(λ: <>, ![go.int] #j_ptr ≥⟨go.int⟩ #(W64 1)))
        glv(λ: <>,
            (if:
                (Convert go.untypedBool go.bool)
                  ((GoUnOp GoNot go.bool)
                    ((let: "$a0" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                        let: "$a1" :=
                          ![Et]
                            ((IndexRef Et.SliceType)
                              (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
                          (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0") "$a1") <⟨go.int⟩
                      #(W64 0))) then
                doBreak #() else do: #()) ;;;
              let: "$r0" :=
                ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
                let: "$r1" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                  do: (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr) <-[Et] "$r0" ;;;
                    do:
                      (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1)) <-[Et]
                        "$r1"))
      glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1)))
      {{ v, ⌜v = executeVal⌝ ∗ ∃ xs3,
        "Hxs" ∷ data ↦* xs3 ∗ "i" ∷ i_ptr ↦ i_val ∗ "a" ∷ a_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ data ∗ "cmp" ∷ cmp_ptr ↦ cmp_code ∗
        "%Hperm3" ∷ ⌜xs ≡ₚ xs3⌝ ∗
        "%Hsorted3" ∷ ⌜IsSortedSeg R xs3 (sint.nat a) (sint.nat i_val)⌝ ∗
        "%Houtside3" ∷ ⌜OutsideSame xs xs3 (sint.nat a) (sint.nat b)⌝ }} := by
  iintro #Hcmp cmp a data i HL
  have hi1 : sint.nat (i_val - W64 1) = sint.nat i_val - 1 := by word
  wp_for HL
  have Header2' := header_preserve R xs xs3 _ _ Header Hperm3 Houtside3 (by word)
  have hlen3 := Hperm3.length_eq
  have hsi : sint.nat i_val - 1 + 1 = sint.nat i_val := by word
  by_cases Hjl : sint.Z (W64 1) ≤ sint.Z jl
  case neg =>
    simp only [Hjl, decide_false, Bool.false_eq_true, ↓reduceIte]
    isplitl []
    · itrivial
    iexists xs3
    iframe
    ipureintro
    refine ⟨Hperm3, ?_, Houtside3⟩
    rw [← hsi]
    exact insBr_done_a R _ _ _ _ HsortedBr (by word)
  simp only [Hjl, _root_.decide_true, ↓reduceIte]
  wp_auto
  list_elem xs3 (sint.nat jl) as y0
  list_elem xs3 (sint.nat (jl - W64 1)) as y1
  have hj1 : sint.nat (jl - W64 1) = sint.nat jl - 1 := by word
  have hjdx : (sint.Z (jl - W64 1)).toNat = sint.nat jl - 1 := hj1
  rw [hj1] at Hy1_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z jl) xs3 _ y0 (by word) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hy0_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z (jl - W64 1)) xs3 _ y1 (by word) $$ [Hxs]
    with Hxs
  · iframe Hxs; ipureintro; rw [hjdx]; exact Hy1_lookup
  wp_apply ins_wp_cmp R cmp_code $$ Hcmp with %r' %Hr'
  by_cases hc' : sint.Z r' < sint.Z (W64 0)
  case neg =>
    -- break
    simp only [hc', decide_false, Bool.not_false]
    cleanup_bool_decide
    wp_auto
    wp_for_post
    isplitl []
    · itrivial
    iexists xs3
    iframe
    ipureintro
    refine ⟨Hperm3, ?_, Houtside3⟩
    rw [← hsi]
    by_cases hja : sint.nat jl = sint.nat a
    · exact insBr_done_a R _ _ _ _ HsortedBr hja
    · exact insBr_done_cmp R _ _ _ _ _ _ HsortedBr (by word) (by word) Hy0_lookup Hy1_lookup
        (fun h => hc' (Hr'.2 h))
  simp only [hc', _root_.decide_true, Bool.not_true]
  cleanup_bool_decide
  wp_auto
  have hRy := Hr'.1 hc'
  have hja : sint.nat a < sint.nat jl := by
    by_cases hja : sint.nat jl = sint.nat a
    · exfalso
      rw [hja] at Hy0_lookup Hy1_lookup
      exact header_contra R _ _ _ _ _ Header2' (by word) (by word) Hy0_lookup Hy1_lookup hRy
    · word
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z (jl - W64 1)) xs3 _ y1 (by word) $$ [Hxs]
    with Hxs
  · iframe Hxs; ipureintro; rw [hjdx]; exact Hy1_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z jl) xs3 _ y0 (by word) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hy0_lookup
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z jl) xs3 y1 $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; word
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z (jl - W64 1)) _ y0 $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp only [List.length_set]; word
  wp_for_post
  iframe
  iexists (jl - W64 1), _
  iframe
  ipureintro
  rw [hjdx, show (sint.Z jl).toNat = sint.nat jl from rfl, hj1]
  refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
  · exact Hperm3.trans (swap_perm _ _ _ _ _ Hy1_lookup Hy0_lookup)
  · exact insBr_swap R _ _ _ _ _ _ HsortedBr hja (by word) Hy0_lookup Hy1_lookup hRy
  · exact outsideSame_trans _ _ _ _ _ Houtside3
      (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)

omit package_sem [StrictWeakOrder R] in
/-- The loop of `partialInsertionSortCmpFunc` that shifts the greater element
`data[i]` to the right (a separate theorem, so that it elaborates in parallel). -/
theorem ins_wp_shift_right (data : GoSlice) (a b i_val : w64) (cmp_code : GoFunc)
    (xs : List E) (cmp_ptr b_ptr data_ptr j_ptr : Loc) (Φ : val → IProp GF)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len)
    (irange : sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) :
    ⊢ cmpImplements R cmp_code -∗ cmp_ptr ↦ cmp_code -∗ b_ptr ↦ b -∗ data_ptr ↦ data -∗
      (∃ (jr : w64) (xs4 : List E),
        "jr" ∷ j_ptr ↦ jr ∗
        "Hxs" ∷ data ↦* xs4 ∗
        "%jrange" ∷ ⌜sint.Z i_val < sint.Z jr ∧ sint.Z jr ≤ sint.Z b⌝ ∗
        "%Hperm4" ∷ ⌜xs ≡ₚ xs4⌝ ∗
        "%Hsorted4" ∷ ⌜IsSortedSeg R xs4 (sint.nat a) (sint.nat i_val)⌝ ∗
        "%Houtside4" ∷ ⌜OutsideSame xs xs4 (sint.nat a) (sint.nat b)⌝ : IProp GF) -∗
      (∀ xs4 : List E, data ↦* xs4 ∗ cmp_ptr ↦ cmp_code ∗ b_ptr ↦ b ∗ data_ptr ↦ data ∗
        ⌜xs ≡ₚ xs4 ∧ IsSortedSeg R xs4 (sint.nat a) (sint.nat i_val) ∧
          OutsideSame xs xs4 (sint.nat a) (sint.nat b)⌝ -∗ Φ executeVal) -∗
      WP (((doFor glv(λ: <>, ![go.int] #j_ptr <⟨go.int⟩ ![go.int] #b_ptr))
        glv(λ: <>,
            (if:
                (Convert go.untypedBool go.bool)
                  ((GoUnOp GoNot go.bool)
                    ((let: "$a0" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                        let: "$a1" :=
                          ![Et]
                            ((IndexRef Et.SliceType)
                              (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
                          (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0") "$a1") <⟨go.int⟩
                      #(W64 0))) then
                doBreak #() else do: #()) ;;;
              let: "$r0" :=
                ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))) in
                let: "$r1" := ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                  do: (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr) <-[Et] "$r0" ;;;
                    do:
                      (IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr -⟨go.int⟩ #(W64 1)) <-[Et]
                        "$r1"))
      glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr +⟨go.int⟩ #(W64 1))) {{ Φ }} := by
  iintro #Hcmp cmp b data HRt HΦ
  wp_for HRt
  have hlen4 := Hperm4.length_eq
  wp_if_destruct
  · list_elem xs4 (sint.nat jr) as y0
    list_elem xs4 (sint.nat (jr - W64 1)) as y1
    have hj1 : sint.nat (jr - W64 1) = sint.nat jr - 1 := by word
    have hjdx : (sint.Z (jr - W64 1)).toNat = sint.nat jr - 1 := hj1
    rw [hj1] at Hy1_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z jr) xs4 _ y0 (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hy0_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z (jr - W64 1)) xs4 _ y1 (by word) $$ [Hxs]
      with Hxs
    · iframe Hxs; ipureintro; rw [hjdx]; exact Hy1_lookup
    wp_apply ins_wp_cmp R cmp_code $$ Hcmp with %r' %Hr'
    by_cases hc' : sint.Z r' < sint.Z (W64 0)
    case neg =>
      -- break
      simp only [hc', decide_false, Bool.not_false]
      cleanup_bool_decide
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact ⟨Hperm4, Hsorted4, Houtside4⟩
    simp only [hc', _root_.decide_true, Bool.not_true]
    cleanup_bool_decide
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z (jr - W64 1)) xs4 _ y1 (by word) $$ [Hxs]
      with Hxs
    · iframe Hxs; ipureintro; rw [hjdx]; exact Hy1_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z jr) xs4 _ y0 (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hy0_lookup
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z jr) xs4 y1 $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; word
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z (jr - W64 1)) _ y0 $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp only [List.length_set]; word
    wp_for_post
    iframe
    iexists (jr + W64 1), _
    iframe
    ipureintro
    rw [hjdx, show (sint.Z jr).toNat = sint.nat jr from rfl]
    refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
    · exact Hperm4.trans (swap_perm _ _ _ _ _ Hy1_lookup Hy0_lookup)
    · exact isSortedSeg_swap_hi R _ _ _ _ _ _ _ Hsorted4 (by word) (by word)
    · exact outsideSame_trans _ _ _ _ _ Houtside4
        (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨Hperm4, Hsorted4, Houtside4⟩

end proof

end slices

end Perennial
end

