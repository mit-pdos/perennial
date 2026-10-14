/-
The pure facts, loop invariants, loop lemmas and proof-script macros of the proofs of
`partitionCmpFunc`, `medianCmpFunc`, `medianAdjacentCmpFunc`, `choosePivotCmpFunc`,
`breakPatternsCmpFunc` and `partitionEqualCmpFunc` (reused by their `Ordered` copies).
-/
module

public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

/-- Formerly `word` plus literal normalization; `word` now does that itself. -/
macro "word_p" : tactic => `(tactic| word)

-- (the proof-script macros come before all proofs: a command such as `macro`
-- declared after asynchronously elaborated proofs waits for them)
set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_loop1" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · iapply (wp_part_loop1 (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr cmp_ptr
      cmp_code Hab_bound Hlen) $$ Hpkg Hcmp a data cmp HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_loop2" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · iapply (wp_part_loop2 (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr cmp_ptr
      cmp_code Hab_bound Hlen) $$ Hpkg Hcmp a data cmp HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionCmpFunc`. -/
macro "part_load_j" : tactic => `(tactic| (
  unfold partInv
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
  exact part_finish_pure R xs xs1 a b i_val j_val xp xj Hab_bound ij_bound Hpart Hpivot HPerm1
    Houtside1 Hlen2 Hxj_lookup Hif))

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
  ihave HI : partInv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    simp only [sint_toNat]
    exact part_swap_pure R xs xs1 a b i_val j_val xp xi xj Hab_bound ij_bound Hpart Hpivot HPerm1
      Houtside1 Hlen2 Hxj_lookup Hle Hxi_lookup HBr1' HBr2'))

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
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

theorem dec_val_true {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P := by
  by_cases hp : P
  · exact hp
  · rw [decide_eq_false hp] at h; exact absurd h false_neq_true

theorem dec_val_false {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #true) : ¬ P :=
  fun hp => h (by rw [decide_eq_true hp])

end bool_lemmas

section pure
variable {E : Type} (R : E → E → Prop)

def IsPartitionedPre (xs : List E) (a b i_val j_val : Nat) : Prop :=
  ∀ (i : Nat) xi xa, xs[i]? = some xi → xs[a]? = some xa →
    ((a < i ∧ i < i_val → ¬ R xa xi) ∧
     (j_val < i ∧ i < b → ¬ R xi xa))

def IsPartitioned (xs : List E) (a b r : Nat) : Prop :=
  ∀ (i : Nat) xr xi, xs[i]? = some xi → xs[r]? = some xr →
    ((a ≤ i ∧ i < r → ¬ R xr xi) ∧
     (r < i ∧ i < b → ¬ R xi xr))

theorem isPartitionedPre_advance_left (xs : List E) (a b i_val j_val : Nat) (xa xi : E) :
    IsPartitionedPre R xs a b i_val j_val →
    xs[a]? = some xa → xs[i_val]? = some xi → ¬ R xa xi →
    IsPartitionedPre R xs a b (i_val + 1) j_val := by
  unfold IsPartitionedPre
  intro H Ha Hi Hai i xi0 xa0 Hxi0 Hxa0
  rw [Ha] at Hxa0; cases Hxa0
  obtain ⟨H1, H2⟩ := H i xi0 xa Hxi0 Ha
  refine ⟨fun hi => ?_, H2⟩
  by_cases h : i = i_val
  · subst h; rw [Hi] at Hxi0; cases Hxi0; exact Hai
  · exact H1 (by omega)

theorem isPartitionedPre_advance_right (xs : List E) (a b i_val j_val : Nat) (xa xj : E) :
    IsPartitionedPre R xs a b i_val j_val →
    xs[a]? = some xa → xs[j_val]? = some xj → ¬ R xj xa →
    IsPartitionedPre R xs a b i_val (j_val - 1) := by
  unfold IsPartitionedPre
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
    IsPartitionedPre R xs a b i_val j_val →
    xs[a]? = some xa → xs[j_val]? = some xj →
    IsPartitioned R (<[a := xj]> (<[j_val := xa]> xs)) a b j_val := by
  unfold IsPartitionedPre IsPartitioned
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
    IsPartitionedPre R xs a b i_val j_val →
    xs[a]? = some xa → xs[i_val]? = some xi → xs[j_val]? = some xj →
    ¬ R xi xa → ¬ R xa xj →
    IsPartitionedPre R (<[j_val := xi]> (<[i_val := xj]> xs)) a b (i_val + 1) (j_val - 1) := by
  unfold IsPartitionedPre
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

def IsEqSeg (xs : List E) (a b : Nat) : Prop :=
  ∀ (i j : Nat) xi xj, (a ≤ i ∧ i < j) ∧ j < b →
    xs[i]? = some xi → xs[j]? = some xj → ¬ R xj xi ∧ ¬ R xi xj

theorem isEqSeg_extend [StrictWeakOrder R] (xs : List E) (a i : Nat) (xp xi : E) :
    xs[a]? = some xp → IsEqSeg R xs a i →
    xs[i]? = some xi →
    ¬ R xi xp ∧ ¬ R xp xi →
    IsEqSeg R xs a (i + 1) := by
  unfold IsEqSeg
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

theorem isEqSeg_is_sorted_seg (xs : List E) (a b : Nat) :
    IsEqSeg R xs a b → IsSortedSeg R xs a b := by
  intro H i j xi xj hb hi hj
  exact (H i j xi xj hb hi hj).1

def IsEqPartitioned (xs : List E) (a b r : Nat) : Prop :=
  ∀ (i j : Nat) xi xj,
    xs[i]? = some xi → xs[j]? = some xj →
      (a ≤ i ∧ (i < j ∧ j < b) ∧ i < r) → ¬ R xj xi

theorem peq_init_min [StrictWeakOrder R] (xs : List E) (a pivot b : Nat) (xp xa : E)
    (hp : xs[pivot]? = some xp) (ha : xs[a]? = some xa) (hab : a ≤ pivot ∧ pivot < b)
    (H : OneLeSeg R xs pivot a b) :
    OneLeSeg R ((xs.set a xp).set pivot xa) a a b := by
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
    (H : OneLeSeg R xs1 a a b) :
    OneLeSeg R ((xs1.set i xj).set j xi) a a b := by
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
    (Hs : IsEqSeg R xs1 a i) (Hmin : OneLeSeg R xs1 a a b) (Hbr2 : ¬ R xp xj) :
    IsEqSeg R ((xs1.set i xj).set j xi) a (i + 1) := by
  apply isEqSeg_extend R _ a i xp xj
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
    (hp : xs1[a]? = some xp) (Hs : IsEqSeg R xs1 a i) (Hmin : OneLeSeg R xs1 a a b) :
    IsEqPartitioned R xs1 a b i := by
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

/-- The loop invariant of `partitionCmpFunc` (`br1`/`br2`
record that the first/second inner loop has exited). -/
def partInv (data : GoSlice) (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : Loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜(sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
                   (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)⌝ ∗
    "%Hpart" ∷ ⌜IsPartitionedPre R xs1 (sint.nat a) (sint.nat b) (sint.nat i_val)
                 (sint.nat j_val)⌝ ∗
    "%Hpivot" ∷ ⌜xs1[sint.nat a]? = some xp⌝ ∗
    "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
    "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ ∗
    "%HBr1" ∷ ⌜br1 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xi, xs1[sint.nat i_val]? = some xi → ¬ R xi xp⌝ ∗
    "%HBr2" ∷ ⌜br2 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xj, xs1[sint.nat j_val]? = some xj → ¬ R xp xj⌝)

/-- The first inner loop of `partitionCmpFunc`
(`for i <= j && cmp(data[i], data[a]) < 0 { i++ }`), which the Go code contains twice. -/
theorem wp_part_loop1 (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr cmp_ptr : Loc) (cmp_code : GoFunc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ cmpImplements R cmp_code -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗ cmp_ptr ↦□ cmp_code -∗
      partInv R data a b xp xs i_ptr j_ptr false false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (let: "$a0" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #i_ptr)) in
                let: "$a1" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                  (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0")
                    "$a1") <⟨go.int⟩
                #(W64 0) else
              #false)))
          (Val glv(λ: <>, do: #i_ptr <-[go.int] ![go.int] #i_ptr +⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        partInv R data a b xp xs i_ptr j_ptr true false) }} := by
  iintro #Hpkg #Hcmp #a #data #cmp HI
  unfold cmpImplements
  unfold partInv
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
      exact isPartitionedPre_advance_left R _ _ _ _ _ xp xi Hpart Hpivot Hxi_lookup
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

/-- The second inner loop of `partitionCmpFunc`
(`for i <= j && !(cmp(data[j], data[a]) < 0) { j-- }`), which the Go code contains twice. -/
theorem wp_part_loop2 (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr cmp_ptr : Loc) (cmp_code : GoFunc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ cmpImplements R cmp_code -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗ cmp_ptr ↦□ cmp_code -∗
      partInv R data a b xp xs i_ptr j_ptr true false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (GoUnOp GoNot go.bool)
                ((let: "$a0" :=
                    ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                    let: "$a1" :=
                      ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                      (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0")
                        "$a1") <⟨go.int⟩
                  #(W64 0)) else
              #false)))
          (Val glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        partInv R data a b xp xs i_ptr j_ptr true true) }} := by
  iintro #Hpkg #Hcmp #a #data #cmp HI
  unfold cmpImplements
  unfold partInv
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
        exact isPartitionedPre_advance_right R _ _ _ _ _ xp xj Hpart Hpivot Hxj_lookup
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

omit [StrictWeakOrder R] ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx [ZeroVal E] in
/-- The pure part of `part_finish`. -/
theorem part_finish_pure [StrictWeakOrder R] (xs xs1 : List E) (a b i_val j_val : w64) (xp xj : E)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ ↑xs.length ∧ xs.length ≤ 2 ^ 62)
    (ij_bound : (sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
      sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)
    (Hpart : IsPartitionedPre R xs1 (sint.nat a) (sint.nat b) (sint.nat i_val) (sint.nat j_val))
    (Hpivot : xs1[sint.nat a]? = some xp) (HPerm1 : xs ≡ₚ xs1)
    (Houtside1 : OutsideSame xs xs1 (sint.nat a) (sint.nat b)) (_Hlen2 : xs.length = xs1.length)
    (Hxj_lookup : xs1[sint.nat j_val]? = some xj) (Hif : sint.Z j_val < sint.Z i_val) :
    (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val < sint.Z b) ∧
    xs ≡ₚ (xs1.set (sint.nat j_val) xp).set (sint.nat a) xj ∧
      IsPartitioned R ((xs1.set (sint.nat j_val) xp).set (sint.nat a) xj) (sint.nat a) (sint.nat b)
        (sint.nat j_val) ∧
        OutsideSame xs ((xs1.set (sint.nat j_val) xp).set (sint.nat a) xj) (sint.nat a)
          (sint.nat b) := by
  refine ⟨by omega, HPerm1.trans (swap_perm xs1 _ _ xp xj Hpivot Hxj_lookup), ?_, ?_⟩
  · exact partition_conclude R xs1 _ _ (sint.nat i_val) _ xp xj (by word) ⟨by word, by word⟩
      Hpart Hpivot Hxj_lookup
  · exact outsideSame_trans _ _ _ _ _ Houtside1
      (outsideSame_swap _ _ _ _ _ _ _ (by word) (by word))

omit [StrictWeakOrder R] ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx [ZeroVal E] in
/-- The pure part of `part_swap`. -/
theorem part_swap_pure [StrictWeakOrder R] (xs xs1 : List E) (a b i_val j_val : w64) (xp xi xj : E)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ ↑xs.length ∧ xs.length ≤ 2 ^ 62)
    (ij_bound : (sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
      sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)
    (Hpart : IsPartitionedPre R xs1 (sint.nat a) (sint.nat b) (sint.nat i_val) (sint.nat j_val))
    (Hpivot : xs1[sint.nat a]? = some xp) (HPerm1 : xs ≡ₚ xs1)
    (Houtside1 : OutsideSame xs xs1 (sint.nat a) (sint.nat b)) (Hlen2 : xs.length = xs1.length)
    (Hxj_lookup : xs1[sint.nat j_val]? = some xj) (Hle : sint.Z i_val ≤ sint.Z j_val)
    (Hxi_lookup : xs1[sint.nat i_val]? = some xi)
    (HBr1' : sint.Z i_val > sint.Z j_val ∨ ∀ (xi : E), xs1[sint.nat i_val]? = some xi → ¬R xi xp)
    (HBr2' : sint.Z i_val > sint.Z j_val ∨ ∀ (xj : E), xs1[sint.nat j_val]? = some xj → ¬R xp xj) :
    ((sint.Z a + 1 ≤ sint.Z (i_val + W64 1) ∧ sint.Z (i_val + W64 1) ≤ sint.Z b) ∧
      sint.Z a ≤ sint.Z (j_val - W64 1) ∧ sint.Z (j_val - W64 1) ≤ sint.Z b - 1) ∧
    IsPartitionedPre R ((xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi) (sint.nat a)
        (sint.nat b) (sint.nat (i_val + W64 1)) (sint.nat (j_val - W64 1)) ∧
      ((xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi)[sint.nat a]? = some xp ∧
        xs ≡ₚ (xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi ∧
          OutsideSame xs ((xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi) (sint.nat a)
            (sint.nat b) ∧
            (false = true →
                sint.Z (i_val + W64 1) > sint.Z (j_val - W64 1) ∨
                  ∀ (xi_1 : E),
                    ((xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi)[sint.nat (i_val + W64 1)]? =
                      some xi_1 → ¬R xi_1 xp) ∧
              (false = true →
                sint.Z (i_val + W64 1) > sint.Z (j_val - W64 1) ∨
                  ∀ (xj_1 : E),
                    ((xs1.set (sint.nat i_val) xj).set (sint.nat j_val) xi)[sint.nat (j_val - W64 1)]? =
                      some xj_1 → ¬R xp xj_1) := by
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
  · exact outsideSame_trans _ _ _ _ _ Houtside1
      (outsideSame_swap _ _ _ _ _ _ _ (by word) (by word))

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- The three sample positions `a + d * k` of `choosePivotCmpFunc` do not overflow. -/
theorem part_choosePivot_idx (a b d : w64) (n : Nat)
    (Hab : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ n ∧ n ≤ 2 ^ 62)
    (Hd : sint.Z d = (sint.Z b - sint.Z a) / 4) :
    sint.Z (a + d * 1) = sint.Z a + sint.Z d ∧ sint.Z (a + d * 2) = sint.Z a + 2 * sint.Z d ∧
    sint.Z (a + d * 3) = sint.Z a + 3 * sint.Z d := by
  refine ⟨?_, ?_, ?_⟩ <;> word_p

/-- The loop invariant of `partitionEqualCmpFunc`. -/
def peqInv (data : GoSlice) (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : Loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜(sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b) ∧
                   (sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z b - 1)⌝ ∗
    "%Hsorted" ∷ ⌜IsEqSeg R xs1 (sint.nat a) (sint.nat i_val)⌝ ∗
    "%Hpivot" ∷ ⌜xs1[sint.nat a]? = some xp⌝ ∗
    "%Hmin" ∷ ⌜OneLeSeg R xs1 (sint.nat a) (sint.nat a) (sint.nat b)⌝ ∗
    "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
    "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ ∗
    "%HBr1" ∷ ⌜br1 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xi, xs1[sint.nat i_val]? = some xi → ¬ R xi xp⌝ ∗
    "%HBr2" ∷ ⌜br2 = true → sint.Z i_val > sint.Z j_val ∨
                 ∀ xj, xs1[sint.nat j_val]? = some xj → ¬ R xp xj⌝)

omit package_sem in
/-- The first inner loop of `partitionEqualCmpFunc` (`for i <= j && !less(data[a], data[i]) { i++ }`). -/
theorem wp_peq_loop1 (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr cmp_ptr : Loc) (cmp_code : GoFunc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ cmpImplements R cmp_code -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗ cmp_ptr ↦□ cmp_code -∗
      peqInv R data a b xp xs i_ptr j_ptr false false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (GoUnOp GoNot go.bool)
                ((let: "$a0" :=
                    ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                    let: "$a1" :=
                      ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #i_ptr)) in
                      (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0")
                        "$a1") <⟨go.int⟩
                  #(W64 0)) else
              #false)))
          (Val glv(λ: <>, do: #i_ptr <-[go.int] ![go.int] #i_ptr +⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        peqInv R data a b xp xs i_ptr j_ptr true false) }} := by
  iintro #Hpkg #Hcmp #a #data #cmp HI
  unfold cmpImplements
  unfold peqInv
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
      exact isEqSeg_extend R xs1 _ _ xp xi Hpivot Hsorted Hxi_lookup
        ⟨Hmin xp _ xi ⟨by word, by word⟩ Hpivot Hxi_lookup,
         fun h => hP (by have := Hr.2 h; word)⟩
  · isplitl []
    · itrivial
    iexists xs1, i_val, j_val
    iframe
    ipureintro
    exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inl (by omega),
      nofun⟩

omit package_sem [StrictWeakOrder R] in
/-- The second inner loop of `partitionEqualCmpFunc` (`for i <= j && less(data[a], data[j]) { j-- }`). -/
theorem wp_peq_loop2 (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr cmp_ptr : Loc) (cmp_code : GoFunc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ cmpImplements R cmp_code -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗ cmp_ptr ↦□ cmp_code -∗
      peqInv R data a b xp xs i_ptr j_ptr true false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (let: "$a0" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                let: "$a1" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                  (![go.FunctionType (go.Signature [Et, Et] false [go.int])] #cmp_ptr "$a0")
                    "$a1") <⟨go.int⟩
                #(W64 0) else
              #false)))
          (Val glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        peqInv R data a b xp xs i_ptr j_ptr true true) }} := by
  iintro #Hpkg #Hcmp #a #data #cmp HI
  unfold cmpImplements
  unfold peqInv
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

end proof

end slices

end Perennial
end

