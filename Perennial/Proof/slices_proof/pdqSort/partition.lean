/-
Port of `new/proof/slices_proof/pdqSort/partition.v`: specs of
`partitionCmpFunc`, `medianCmpFunc`, `medianAdjacentCmpFunc`,
`choosePivotCmpFunc`, `breakPatternsCmpFunc` and `partitionEqualCmpFunc`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.slices
import Perennial.GeneratedProof.slices
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.slices_proof.pdqSort.sort_basics

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

/-- Formerly `word` plus literal normalization; `word` now does that itself. -/
macro "word_p" : tactic => `(tactic| word)

theorem sdiv4_nonneg (x : w64) (h : 0 ≤ sint.Z x) : BitVec.sdiv x (W64 4) = x / (4 : w64) := by
  have hm : x.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by word)
  simp only [W64]
  unfold BitVec.sdiv
  rw [hm, show (BitVec.ofInt 64 4).msb = false from rfl]
  rfl

theorem sint_sdiv4 (x : w64) (h : 0 ≤ sint.Z x) :
    sint.Z (BitVec.sdiv x (W64 4)) = sint.Z x / 4 := by
  rw [sdiv4_nonneg x h]
  word_p

theorem sint_toNat (x : w64) : (sint.Z x).toNat = sint.nat x := rfl

theorem W64_1 : W64 1 = (1 : w64) := by decide
theorem W64_2 : W64 2 = (2 : w64) := by decide
theorem W64_3 : W64 3 = (3 : w64) := by decide

section bool_lemmas
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

theorem dec_val_true {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P := by
  by_cases hp : P
  · exact hp
  · rw [decide_eq_false hp] at h; exact absurd h false_neq_true

theorem dec_val_false {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #true) : ¬ P :=
  fun hp => h (by rw [decide_eq_true hp])

end bool_lemmas

section pure
variable {E : Type} (R : E → E → Prop)

def is_partitioned_pre (xs : List E) (a b i_val j_val : Nat) : Prop :=
  ∀ (i : Nat) xi xa, xs[i]? = some xi → xs[a]? = some xa →
    ((a < i ∧ i < i_val → ¬ R xa xi) ∧
     (j_val < i ∧ i < b → ¬ R xi xa))

def is_partitioned (xs : List E) (a b r : Nat) : Prop :=
  ∀ (i : Nat) xr xi, xs[i]? = some xi → xs[r]? = some xr →
    ((a ≤ i ∧ i < r → ¬ R xr xi) ∧
     (r < i ∧ i < b → ¬ R xi xr))

theorem is_partitioned_pre_advance_left (xs : List E) (a b i_val j_val : Nat) (xa xi : E) :
    is_partitioned_pre R xs a b i_val j_val →
    xs[a]? = some xa → xs[i_val]? = some xi → ¬ R xa xi →
    is_partitioned_pre R xs a b (i_val + 1) j_val := by
  unfold is_partitioned_pre
  intro H Ha Hi Hai i xi0 xa0 Hxi0 Hxa0
  rw [Ha] at Hxa0; cases Hxa0
  obtain ⟨H1, H2⟩ := H i xi0 xa Hxi0 Ha
  refine ⟨fun hi => ?_, H2⟩
  by_cases h : i = i_val
  · subst h; rw [Hi] at Hxi0; cases Hxi0; exact Hai
  · exact H1 (by omega)

theorem is_partitioned_pre_advance_right (xs : List E) (a b i_val j_val : Nat) (xa xj : E) :
    is_partitioned_pre R xs a b i_val j_val →
    xs[a]? = some xa → xs[j_val]? = some xj → ¬ R xj xa →
    is_partitioned_pre R xs a b i_val (j_val - 1) := by
  unfold is_partitioned_pre
  intro H Ha Hj Hja i xi0 xa0 Hxi0 Hxa0
  rw [Ha] at Hxa0; cases Hxa0
  obtain ⟨H1, H2⟩ := H i xi0 xa Hxi0 Ha
  refine ⟨H1, fun hi => ?_⟩
  by_cases h : i = j_val
  · subst h; rw [Hj] at Hxi0; cases Hxi0; exact Hja
  · exact H2 (by omega)

theorem partition_conclude (xs : List E) (a b i_val j_val : Nat) (xa xj : E) :
    i_val > j_val →
    (a < i_val ∧ j_val ≥ a) →
    is_partitioned_pre R xs a b i_val j_val →
    xs[a]? = some xa → xs[j_val]? = some xj →
    is_partitioned R (<[a := xj]> (<[j_val := xa]> xs)) a b j_val := by
  unfold is_partitioned_pre is_partitioned
  intro Hij Hb H Ha Hj i xr xi Hxi Hxr
  have hjl := lookup_lt_Some Hj
  have hal := lookup_lt_Some Ha
  have hxr : xr = xa := by
    by_cases h : a = j_val
    · subst h
      rw [list_lookup_insert_eq _ (by simp; omega)] at Hxr
      rw [Ha] at Hj; cases Hj; cases Hxr; rfl
    · rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_eq _ (by omega)] at Hxr
      cases Hxr; rfl
  subst hxr
  constructor
  · intro hi
    by_cases h : a = i
    · subst h
      rw [list_lookup_insert_eq _ (by simp; omega)] at Hxi
      cases Hxi
      exact (H j_val xj xr Hj Ha).1 (by omega)
    · rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)] at Hxi
      exact (H i xi xr Hxi Ha).1 (by omega)
  · intro hi
    rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)] at Hxi
    exact (H i xi xr Hxi Ha).2 (by omega)

theorem partition_restore_invariant (xs : List E) (a b i_val j_val : Nat) (xi xj xa : E) :
    (a < i_val ∧ i_val ≤ j_val) ∧ j_val < b ∧ b ≤ xs.length →
    is_partitioned_pre R xs a b i_val j_val →
    xs[a]? = some xa → xs[i_val]? = some xi → xs[j_val]? = some xj →
    ¬ R xi xa → ¬ R xa xj →
    is_partitioned_pre R (<[j_val := xi]> (<[i_val := xj]> xs)) a b (i_val + 1) (j_val - 1) := by
  unfold is_partitioned_pre
  intro Hb H Ha Hi Hj Hia Haj i xi0 xa0 Hxi0 Hxa0
  rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega), Ha] at Hxa0
  cases Hxa0
  by_cases h : i = j_val
  · subst h
    rw [list_lookup_insert_eq _ (by simp; omega)] at Hxi0
    cases Hxi0
    by_cases h' : i_val = i
    · subst h'; rw [Hi] at Hj; cases Hj; exact ⟨fun _ => Haj, fun _ => Hia⟩
    · exact ⟨fun _ => by omega, fun _ => Hia⟩
  · rw [list_lookup_insert_ne _ _ (by omega)] at Hxi0
    by_cases h' : i_val = i
    · subst h'
      rw [list_lookup_insert_eq _ (by omega)] at Hxi0
      cases Hxi0
      exact ⟨fun _ => Haj, fun _ => by omega⟩
    · rw [list_lookup_insert_ne _ _ (by omega)] at Hxi0
      obtain ⟨H1, H2⟩ := H i xi0 xa Hxi0 Ha
      exact ⟨fun hi => H1 (by omega), fun hi => H2 (by omega)⟩

def is_eq_seg (xs : List E) (a b : Nat) : Prop :=
  ∀ (i j : Nat) xi xj, (a ≤ i ∧ i < j) ∧ j < b →
    xs[i]? = some xi → xs[j]? = some xj → ¬ R xj xi ∧ ¬ R xi xj

theorem is_eq_seg_extend [StrictWeakOrder R] (xs : List E) (a i : Nat) (xp xi : E) :
    xs[a]? = some xp → is_eq_seg R xs a i →
    xs[i]? = some xi →
    ¬ R xi xp ∧ ¬ R xp xi →
    is_eq_seg R xs a (i + 1) := by
  unfold is_eq_seg
  intro Hp H Hi Hip i0 j xi0 xj Hb Hxi0 Hxj
  have eqv := (StrictWeakOrder.strict_weak_order_equiv (R := R))
  by_cases h : i = j
  · subst h
    rw [Hi] at Hxj; cases Hxj
    have h2 : ¬ R xp xi0 ∧ ¬ R xi0 xp := by
      by_cases ha : i0 = a
      · subst ha; rw [Hp] at Hxi0; cases Hxi0
        exact ⟨notR_refl R _, notR_refl R _⟩
      · have := H a i0 xp xi0 ⟨⟨by omega, by omega⟩, by omega⟩ Hp Hxi0
        exact ⟨this.2, this.1⟩
    exact eqv.trans Hip h2
  · exact H i0 j xi0 xj ⟨Hb.1, by omega⟩ Hxi0 Hxj

theorem is_eq_seg__is_sorted_seg (xs : List E) (a b : Nat) :
    is_eq_seg R xs a b → is_sorted_seg R xs a b := by
  intro H i j xi xj hb hi hj
  exact (H i j xi xj hb hi hj).1

def is_eq_partitioned (xs : List E) (a b r : Nat) : Prop :=
  ∀ (i j : Nat) xi xj,
    xs[i]? = some xi → xs[j]? = some xj →
      (a ≤ i ∧ (i < j ∧ j < b) ∧ i < r) → ¬ R xj xi

theorem peq_init_min [StrictWeakOrder R] (xs : List E) (a pivot b : Nat) (xp xa : E)
    (hp : xs[pivot]? = some xp) (ha : xs[a]? = some xa) (hab : a ≤ pivot ∧ pivot < b)
    (H : one_le_seg R xs pivot a b) :
    one_le_seg R ((xs.set a xp).set pivot xa) a a b := by
  intro x0 j xj hj hx0 hxj
  have hal := lookup_lt_Some ha
  have hpl := lookup_lt_Some hp
  have hx0' : x0 = xp := by
    by_cases h : pivot = a
    · subst h
      rw [list_lookup_insert_eq _ (by simp; omega)] at hx0
      rw [hp] at ha; cases ha; cases hx0; rfl
    · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by omega)] at hx0
      cases hx0; rfl
  subst x0
  by_cases hjp : pivot = j
  · subst hjp
    rw [list_lookup_insert_eq _ (by simp; omega)] at hxj
    cases hxj
    exact H xp a xa ⟨by omega, by omega⟩ hp ha
  · rw [list_lookup_insert_ne _ _ hjp] at hxj
    by_cases hja : a = j
    · subst hja
      rw [list_lookup_insert_eq _ (by omega)] at hxj
      cases hxj
      exact notR_refl R _
    · rw [list_lookup_insert_ne _ _ hja] at hxj
      exact H xp j xj hj hp hxj

theorem peq_swap_min (xs1 : List E) (a b i j : Nat) (xi xj : E)
    (hi : xs1[i]? = some xi) (hj : xs1[j]? = some xj) (hb : a < i ∧ i ≤ j ∧ j < b)
    (H : one_le_seg R xs1 a a b) :
    one_le_seg R ((xs1.set i xj).set j xi) a a b := by
  intro x0 k xk hk hx0 hxk
  rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)] at hx0
  by_cases hjk : j = k
  · subst hjk
    rw [list_lookup_insert_eq _ (by have := lookup_lt_Some hj; simp; omega)] at hxk
    cases hxk
    exact H x0 i xi ⟨by omega, by omega⟩ hx0 hi
  · rw [list_lookup_insert_ne _ _ hjk] at hxk
    by_cases hik : i = k
    · subst hik
      rw [list_lookup_insert_eq _ (by have := lookup_lt_Some hi; omega)] at hxk
      cases hxk
      exact H x0 j xj ⟨by omega, by omega⟩ hx0 hj
    · rw [list_lookup_insert_ne _ _ hik] at hxk
      exact H x0 k xk hk hx0 hxk

theorem peq_swap_seg [StrictWeakOrder R] (xs1 : List E) (a b i j : Nat) (xi xj xp : E)
    (hi : xs1[i]? = some xi) (hj : xs1[j]? = some xj) (hp : xs1[a]? = some xp)
    (hb : a < i ∧ i ≤ j ∧ j < b)
    (Hs : is_eq_seg R xs1 a i) (Hmin : one_le_seg R xs1 a a b) (Hbr2 : ¬ R xp xj) :
    is_eq_seg R ((xs1.set i xj).set j xi) a (i + 1) := by
  apply is_eq_seg_extend R _ a i xp xj
  · rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)]; exact hp
  · intro i0 j0 x0 y0 hb0 hx0 hy0
    rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)] at hx0 hy0
    exact Hs i0 j0 x0 y0 hb0 hx0 hy0
  · by_cases hij : i = j
    · subst hij
      rw [hi] at hj; cases hj
      rw [list_lookup_insert_eq _ (by have := lookup_lt_Some hi; simp; omega)]
    · rw [list_lookup_insert_ne _ _ (Ne.symm hij),
        list_lookup_insert_eq _ (by have := lookup_lt_Some hi; omega)]
  · exact ⟨Hmin xp j xj ⟨by omega, by omega⟩ hp hj, Hbr2⟩

theorem peq_conclude [StrictWeakOrder R] (xs1 : List E) (a b i : Nat) (xp : E)
    (hp : xs1[a]? = some xp) (Hs : is_eq_seg R xs1 a i) (Hmin : one_le_seg R xs1 a a b) :
    is_eq_partitioned R xs1 a b i := by
  intro i' j' xi xj hxi hxj hb
  by_cases hj : j' < i
  · exact (Hs i' j' xi xj ⟨⟨hb.1, hb.2.1.1⟩, hj⟩ hxi hxj).1
  · have heq : ¬ R xi xp ∧ ¬ R xp xi := by
      by_cases ha : i' = a
      · subst ha; rw [hp] at hxi; cases hxi; exact ⟨notR_refl R _, notR_refl R _⟩
      · have := Hs a i' xp xi ⟨⟨by omega, by omega⟩, hb.2.2⟩ hp hxi
        exact ⟨this.1, this.2⟩
    exact notR_trans R xi xp xj (Hmin xp j' xj ⟨by omega, hb.2.1.2⟩ hp hxj) heq.2

end pure

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.type}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

/-- The loop invariant of `partitionCmpFunc` (Rocq `HI0`/`HI1`/`HI2`; `br1`/`br2`
record that the first/second inner loop has exited). -/
def part_inv (data : slice.t) (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜(sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
                   (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)⌝ ∗
    "%Hpart" ∷ ⌜is_partitioned_pre R xs1 (sint.nat a) (sint.nat b) (sint.nat i_val)
                 (sint.nat j_val)⌝ ∗
    "%Hpivot" ∷ ⌜xs1[sint.nat a]? = some xp⌝ ∗
    "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
    "%Houtside1" ∷ ⌜outside_same xs xs1 (sint.nat a) (sint.nat b)⌝ ∗
    "%HBr1" ∷ ⌜br1 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xi, xs1[sint.nat i_val]? = some xi → ¬ R xi xp⌝ ∗
    "%HBr2" ∷ ⌜br2 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xj, xs1[sint.nat j_val]? = some xj → ¬ R xp xj⌝)

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_loop1" : tactic => `(tactic| (
  wp_bind (App (App (App (Val do_for) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = execute_val⌝ ∗
    part_inv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · unfold part_inv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat i_val) as xi
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxi_lookup
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z a) xs1 _ xp (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hpivot
      wp_apply Hcmp with %r %Hr
      wp_if_destruct
      · have hP := dec_val_true Hif
        wp_for_post
        iframe
        iexists xs1, (i_val + W64 1), j_val
        iframe
        ipureintro
        refine ⟨by word, ?_, Hpivot, HPerm1, Houtside1, fun h => h.elim, fun h => h.elim⟩
        rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
        exact is_partitioned_pre_advance_left R _ _ _ _ _ xp xi Hpart Hpivot Hxi_lookup
          (R_antisym R _ _ (Hr.1 (by word)))
      · have hP := dec_val_false Hif
        simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => Or.inr ?_, fun h => h.elim⟩
        intro xi' hxi'
        rw [Hxi_lookup] at hxi'; cases hxi'
        exact fun h => hP (by have := Hr.2 h; word)
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => Or.inl (by omega),
        fun h => h.elim⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_loop2" : tactic => `(tactic| (
  wp_bind (App (App (App (Val do_for) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = execute_val⌝ ∗
    part_inv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · unfold part_inv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat j_val) as xj
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxj_lookup
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z a) xs1 _ xp (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hpivot
      wp_apply Hcmp with %r %Hr
      by_cases hP : sint.Z r < sint.Z (W64 0)
      · -- `data[j] < data[a]`: exit
        simp only [hP, decide_true, Bool.not_true]
        cleanup_bool_decide
        wp_pures
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => HBr1 rfl, fun _ => Or.inr ?_⟩
        intro xj' hxj'
        rw [Hxj_lookup] at hxj'; cases hxj'
        exact R_antisym R _ _ (Hr.1 (by word))
      · simp only [hP, decide_false, Bool.not_false]
        cleanup_bool_decide
        wp_auto
        wp_for_post
        iframe
        iexists xs1, i_val, (j_val - W64 1)
        iframe
        ipureintro
        refine ⟨by word, ?_, Hpivot, HPerm1, Houtside1, fun _ => ?_, fun h => h.elim⟩
        · rw [show sint.nat (j_val - W64 1) = sint.nat j_val - 1 by word]
          exact is_partitioned_pre_advance_right R _ _ _ _ _ xp xj Hpart Hpivot Hxj_lookup
            (fun h => hP (by have := Hr.2 h; word))
        · rcases HBr1 rfl with h | h
          · left; word
          · right; exact h
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => HBr1 rfl,
        fun _ => Or.inl (by omega)⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_load_j" : tactic => `(tactic| (
  unfold part_inv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  list_elem xs1 (sint.nat j_val) as xj
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_finish" : tactic => `(tactic| (
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs1 _ xp (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hpivot
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxj_lookup
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z j_val) xs1 xp $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z a) _ xj $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  wp_auto
  iapply HΦ
  iframe Hxs
  ipureintro
  simp only [sint_toNat]
  refine ⟨by omega, HPerm1.trans (swap_perm xs1 _ _ xp xj Hpivot Hxj_lookup), ?_, ?_⟩
  · exact partition_conclude R xs1 _ _ (sint.nat i_val) _ xp xj (by word) ⟨by word, by word⟩
      Hpart Hpivot Hxj_lookup
  · exact outside_same_trans _ _ _ _ _ Houtside1
      (outside_same_swap _ _ _ _ _ _ _ (by word) (by word))))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_swap" : tactic => `(tactic| (
  have Hle : sint.Z i_val ≤ sint.Z j_val := by word
  obtain ⟨xi, Hxi_lookup⟩ := lookup_lt_is_Some_2 (l := xs1) (i := sint.nat i_val) (by word)
  have HBr1' := HBr1 rfl
  have HBr2' := HBr2 rfl
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxj_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxi_lookup
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z i_val) xs1 xj $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z j_val) _ xi $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  try wp_auto
  ihave HI : part_inv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold part_inv
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, HPerm1.trans (swap_perm xs1 _ _ xj xi Hxj_lookup Hxi_lookup), ?_,
      nofun, nofun⟩
    · rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word,
        show sint.nat (j_val - W64 1) = sint.nat j_val - 1 by word]
      refine partition_restore_invariant R xs1 _ _ _ _ xi xj xp ⟨⟨by word, by word⟩, by word, by word⟩
        Hpart Hpivot Hxi_lookup Hxj_lookup ?_ ?_
      · rcases HBr1' with h | h
        · omega
        · exact h xi Hxi_lookup
      · rcases HBr2' with h | h
        · omega
        · exact h xj Hxj_lookup
    · rw [list_lookup_insert_ne _ _ (by word), list_lookup_insert_ne _ _ (by word)]
      exact Hpivot
    · exact outside_same_trans _ _ _ _ _ Houtside1
        (outside_same_swap _ _ _ _ _ _ _ (by word) (by word))))

set_option maxHeartbeats 600000 in
theorem wp_partitionCmpFunc (data : slice.t) (a b pivot : w64) (cmp_code : func.t)
    (xs : List E) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmp_implements R cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (App (Val #(functions partitionCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #pivot)) (Val #cmp_code))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜is_partitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜outside_same xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := own_slice_len _ _ _ $$ Hxs
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z pivot) xs _ xp (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxp_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs _ xa (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa_lookup
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z a) xs xp $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z pivot) _ xa $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  wp_auto
  ipersist a
  ipersist data
  ipersist cmp
  unfold cmp_implements
  ihave HI : part_inv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold part_inv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outside_same_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i xi xa' _ _; constructor <;> intro <;> word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
  part_loop1
  part_loop2
  part_load_j
  wp_if_destruct
  · part_finish
  · part_swap
    clear Hpart Hpivot HPerm1 Houtside1 HBr1 HBr2 HBr1' HBr2' Hlen2 Hxi_lookup Hxj_lookup ij_bound Hif Hle
      xs1 i_val j_val xi xj
    wp_for
    part_loop1
    part_loop2
    part_load_j
    wp_if_destruct
    · wp_for_post
      part_finish
    · part_swap
      wp_for_post
      unfold part_inv
      simp only [Bool.false_eq_true]
      iframe

theorem wp_medianCmpFunc (data : slice.t) (a b c : w64) (swaps_l : loc) (cmp_code : func.t)
    (dq : DFrac) (xs : List E) (swaps : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(0 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int)) ∧
                      (0 ≤ sint.Z b ∧ sint.Z b < (xs.length : Int)) ∧
                      (0 ≤ sint.Z c ∧ sint.Z c < (xs.length : Int))⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hcmp" ∷ cmp_implements R cmp_code }}
      (App (App (App (App (App (App (Val #(functions medianCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #c)) (Val #swaps_l)) (Val #cmp_code))
    {{ (r : w64) (swaps' : w64), RET #r;
        data ↦*{dq} xs ∗
        ⌜r = a ∨ r = b ∨ r = c⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat a) as xa
  list_elem xs (sint.nat b) as xb
  list_elem xs (sint.nat c) as xc
  wp_apply wp_order2CmpFunc R data a b swaps_l cmp_code dq xs swaps xa xb (by omega) (by omega)
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2CmpFunc R data b c swaps_l cmp_code dq xs sw1 xb xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2CmpFunc R data a b swaps_l cmp_code dq xs sw2 xa xb (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2CmpFunc R data a c swaps_l cmp_code dq xs sw2 xa xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2CmpFunc R data a c swaps_l cmp_code dq xs sw1 xa xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2CmpFunc R data b a swaps_l cmp_code dq xs sw2 xb xa (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2CmpFunc R data b c swaps_l cmp_code dq xs sw2 xb xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

theorem wp_medianAdjacentCmpFunc (data : slice.t) (a : w64) (swaps_l : loc) (cmp_code : func.t)
    (dq : DFrac) (xs : List E) (swaps : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hcmp" ∷ cmp_implements R cmp_code }}
      (App (App (App (App (Val #(functions medianAdjacentCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #swaps_l)) (Val #cmp_code))
    {{ (r : w64) (swaps' : w64), RET #r;
        data ↦*{dq} xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_medianCmpFunc R data (a - W64 1) a (a + W64 1) swaps_l cmp_code dq xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

theorem wp_choosePivotCmpFunc (data : slice.t) (a b : w64) (cmp_code : func.t) (xs : List E) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmp_implements R cmp_code ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions choosePivotCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #cmp_code))
    {{ (r : w64) (hint : slices.sortedHint.t), RET (PairV #r #hint);
        data ↦* xs ∗
        "%Hr_bound" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  have Hl : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have Hd := sint_sdiv4 (b - a) (by omega)
  rw [Hl] at Hd
  generalize BitVec.sdiv (b - a) (W64 4) = d at Hd ⊢
  simp only [W64_1, W64_2, W64_3]
  have Hi : sint.Z (a + d * 1) = sint.Z a + sint.Z d := by word_p
  have Hj : sint.Z (a + d * 2) = sint.Z a + 2 * sint.Z d := by word_p
  have Hk : sint.Z (a + d * 3) = sint.Z a + 3 * sint.Z d := by word_p
  wp_if_destruct
  · have h8 : 8 ≤ sint.Z b - sint.Z a := by word
    wp_if_destruct
    · wp_apply wp_medianAdjacentCmpFunc R data (a + d * 1) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %ri %sw1 ⟨Hxs, %Hri, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi]; omega
      wp_apply wp_medianAdjacentCmpFunc R data (a + d * 2) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rj %sw2 ⟨Hxs, %Hrj, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hj]; omega
      wp_apply wp_medianAdjacentCmpFunc R data (a + d * 3) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rk %sw3 ⟨Hxs, %Hrk, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hk]; omega
      rw [Hi] at Hri; rw [Hj] at Hrj; rw [Hk] at Hrk
      wp_apply wp_medianCmpFunc R data ri rj rk swaps_ptr cmp_code (DFrac.own 1) xs _
        $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
    · wp_apply wp_medianCmpFunc R data (a + d * 1) (a + d * 2) (a + d * 3) swaps_ptr
        cmp_code (DFrac.own 1) xs _ $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi, Hj, Hk]; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
  · have : sint.Z a ≤ sint.Z (a + d * 2) ∧ sint.Z (a + d * 2) < sint.Z b := by
      rw [Hj]; omega
    (try wp_if_destruct) <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)

theorem wp_breakPatternsCmpFunc (data : slice.t) (a b : w64) (cmp_code : func.t) (xs : List E) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmp_implements R cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (App (Val #(functions breakPatternsCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Houtside" ∷ ⌜outside_same xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  sorry -- Rocq: Admitted

/-- The loop invariant of `partitionEqualCmpFunc`. -/
def peq_inv (data : slice.t) (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜(sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
                   (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)⌝ ∗
    "%Hsorted" ∷ ⌜is_eq_seg R xs1 (sint.nat a) (sint.nat i_val)⌝ ∗
    "%Hpivot" ∷ ⌜xs1[sint.nat a]? = some xp⌝ ∗
    "%Hmin" ∷ ⌜one_le_seg R xs1 (sint.nat a) (sint.nat a) (sint.nat b)⌝ ∗
    "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
    "%Houtside1" ∷ ⌜outside_same xs xs1 (sint.nat a) (sint.nat b)⌝ ∗
    "%HBr1" ∷ ⌜br1 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xi, xs1[sint.nat i_val]? = some xi → ¬ R xi xp⌝ ∗
    "%HBr2" ∷ ⌜br2 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xj, xs1[sint.nat j_val]? = some xj → ¬ R xp xj⌝)

set_option maxHeartbeats 600000 in
theorem wp_partitionEqualCmpFunc (data : slice.t) (a b pivot : w64) (cmp_code : func.t)
    (xs : List E) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmp_implements R cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ ∗
        "%Hmin" ∷ ⌜one_le_seg R xs (sint.nat pivot) (sint.nat a) (sint.nat b)⌝ }}
      (App (App (App (App (App (Val #(functions partitionEqualCmpFunc [Et])) (Val #data))
        (Val #a)) (Val #b)) (Val #pivot)) (Val #cmp_code))
    {{ (xs' : List E) (r : w64), RET #r;
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a < sint.Z r ∧ sint.Z r ≤ sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜is_eq_partitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜outside_same xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := own_slice_len _ _ _ $$ Hxs
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z pivot) xs _ xp (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxp_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs _ xa (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa_lookup
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z a) xs xp $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  slice_index_if
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z pivot) _ xa $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  wp_auto
  ipersist a
  ipersist data
  ipersist cmp
  unfold cmp_implements
  ihave HI : peq_inv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold peq_inv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outside_same_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i j xi xj hb; word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact peq_init_min R xs _ _ _ xp xa Hxp_lookup Hxa_lookup ⟨by word, by word⟩ Hmin
  wp_for
  -- first inner loop: `for i <= j && !less(data[a], data[i]) { i++ }`
  wp_bind (App (App (App (Val do_for) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = execute_val⌝ ∗
    peq_inv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · unfold peq_inv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat i_val) as xi
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z a) xs1 _ xp (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hpivot
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxi_lookup
      wp_apply Hcmp with %r %Hr
      by_cases hP : sint.Z r < sint.Z (W64 0)
      · -- `data[a] < data[i]`: exit
        simp only [hP, decide_true, Bool.not_true]
        cleanup_bool_decide
        wp_pures
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inr ?_, nofun⟩
        intro xi' hxi'
        rw [Hxi_lookup] at hxi'; cases hxi'
        exact R_antisym R _ _ (Hr.1 (by word))
      · simp only [hP, decide_false, Bool.not_false]
        cleanup_bool_decide
        wp_auto
        wp_for_post
        iframe
        iexists xs1, (i_val + W64 1), j_val
        iframe
        ipureintro
        refine ⟨by word, ?_, Hpivot, Hmin, HPerm1, Houtside1, nofun, nofun⟩
        rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
        exact is_eq_seg_extend R xs1 _ _ xp xi Hpivot Hsorted Hxi_lookup
          ⟨Hmin xp _ xi ⟨by word, by word⟩ Hpivot Hxi_lookup,
           fun h => hP (by have := Hr.2 h; word)⟩
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inl (by omega),
        nofun⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  -- second inner loop: `for i <= j && less(data[a], data[j]) { j-- }`
  wp_bind (App (App (App (Val do_for) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = execute_val⌝ ∗
    peq_inv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · unfold peq_inv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat j_val) as xj
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z a) xs1 _ xp (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hpivot
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxj_lookup
      wp_apply Hcmp with %r %Hr
      wp_if_destruct
      · have hP := dec_val_true Hif
        wp_for_post
        iframe
        iexists xs1, i_val, (j_val - W64 1)
        iframe
        ipureintro
        refine ⟨by word, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => ?_, nofun⟩
        rcases HBr1 rfl with h | h
        · left; word
        · right; exact h
      · have hP := dec_val_false Hif
        simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
          fun _ => Or.inr ?_⟩
        intro xj' hxj'
        rw [Hxj_lookup] at hxj'; cases hxj'
        exact fun h => hP (by have := Hr.2 h; word)
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
        fun _ => Or.inl (by omega)⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  unfold peq_inv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  wp_auto
  wp_if_destruct
  · -- break; return `i`
    wp_for_post
    iapply HΦ
    iframe Hxs
    ipureintro
    exact ⟨⟨by omega, by omega⟩, HPerm1, peq_conclude R xs1 _ _ _ xp Hpivot Hsorted Hmin,
      Houtside1⟩
  · have Hle : sint.Z i_val ≤ sint.Z j_val := by word
    list_elem xs1 (sint.nat j_val) as xj
    list_elem xs1 (sint.nat i_val) as xi
    have HBr1' := HBr1 rfl
    have HBr2' := HBr2 rfl
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxj_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxi_lookup
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z i_val) xs1 xj $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; omega
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z j_val) _ xi $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp; omega
    try wp_auto
    wp_for_post
    iframe
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    simp only [sint_toNat]
    have hbr2 : ¬ R xp xj := by
      rcases HBr2' with h | h
      · omega
      · exact h xj Hxj_lookup
    refine ⟨by word, ?_, ?_, ?_, HPerm1.trans (swap_perm xs1 _ _ xj xi Hxj_lookup Hxi_lookup), ?_,
      nofun, nofun⟩
    · rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
      exact peq_swap_seg R xs1 _ _ _ _ xi xj xp Hxi_lookup Hxj_lookup Hpivot
        ⟨by word, by word, by word⟩ Hsorted Hmin hbr2
    · rw [list_lookup_insert_ne _ _ (by word), list_lookup_insert_ne _ _ (by word)]
      exact Hpivot
    · exact peq_swap_min R xs1 _ _ _ _ xi xj Hxi_lookup Hxj_lookup ⟨by word, by word, by word⟩ Hmin
    · exact outside_same_trans _ _ _ _ _ Houtside1
        (outside_same_swap _ _ _ _ _ _ _ (by word) (by word))

end proof

end slices

end Perennial
end

