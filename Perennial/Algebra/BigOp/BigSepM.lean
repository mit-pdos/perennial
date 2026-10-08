/-
Extra lemmas about `[∗map]` (and `[∗map]` over two maps) that iris-lean's
`Iris.BI.BigOp.BigSepMap{,2}` does not provide, plus the finite-map facts
(filter, zip, curry) they need.

Conventions:
* Maps are any iris-lean `LawfulFiniteMap M K` (with `DecidableEq K`), so the
  lemmas apply to `Perennial.gmap`. Equality of domains is stated as
  `PartialMap.dom m1 = PartialMap.dom m2` (domains as predicates; see
  `map_dom_eq_iff`), and `mapZip` is an abbreviation for the
  `zipWith (·, ·)` that iris-lean's `bigSepM2` is defined with.
* `big_sepS_exists_sepM` is stated for any iris-lean `LawfulFiniteSet`, with
  `dom m = s` as `FiniteMap.dom_set m = s`.
* `big_sepM_mono_{fupd,bupd}` use `-∗` for the pure premise (equivalent to `→`
  under `□`).
* Filters by a key predicate `P : K → Prop` are written
  `filter (fun k _ => decide (P k)) m`; the complement uses `decide (¬ P k)`.
* There are no `ncfupd` variants (no crash logic, see README.md).
* `map_curry` lemmas are stated for `Perennial.gmap` with a local definition
  `gmapCurry`, since iris-lean has no `map_curry`.
* `big_sepM2_lookup_*` and `big_sepM2_sepM_*` need no `Absorbing` arguments.
-/
module

public import Iris.BI
public import Iris.BI.BigOp
public import Iris.ProofMode
public import Iris.Std.PartialMap
public import Iris.Std.GenSets
public import Perennial.Std.GMap

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.Std BigSepM BigSepM2 BigSepS PartialMap LawfulPartialMap LawfulFiniteMap

/-! ## Map filter -/

section filter

variable {K : Type _} {M : Type u → Type _} [LawfulFiniteMap M K] [DecidableEq K]
variable {A B C : Type u}

theorem map_dom_eq_iff {m1 : M A} {m2 : M B} :
    dom m1 = dom m2 ↔ ∀ k, (get? m1 k).isSome = (get? m2 k).isSome := by
  constructor
  · intro h k
    have := congrFun h k
    simp only [dom] at this
    cases h1 : (get? m1 k).isSome <;> cases h2 : (get? m2 k).isSome <;> simp_all
  · intro h; funext k; simp only [dom, h k]

theorem map_dom_eq_none {m1 : M A} {m2 : M B} (h : dom m1 = dom m2) {k : K} :
    get? m1 k = none ↔ get? m2 k = none := by
  have := map_dom_eq_iff.mp h k
  cases h1 : get? m1 k <;> cases h2 : get? m2 k <;> simp_all

theorem mapLookup_filter_key_in (m : M A) (P : K → Prop) [DecidablePred P] (i : K) :
    P i → get? (filter (fun k _ => decide (P k)) m) i = get? m i := by
  intro hP
  rw [get?_filter]
  cases get? m i <;> simp [hP]

theorem mapLookup_filter_key_notin (m : M A) (P : K → Prop) [DecidablePred P] (i : K) :
    ¬ P i → get? (filter (fun k _ => decide (P k)) m) i = none := by
  intro hP
  rw [get?_filter]
  cases get? m i <;> simp [hP]

theorem mapLookup_filter_key (m : M A) (P : K → Prop) [DecidablePred P] (i : K) :
    get? (filter (fun k _ => decide (P k)) m) i = if P i then get? m i else none := by
  split
  · exact mapLookup_filter_key_in m P i ‹_›
  · exact mapLookup_filter_key_notin m P i ‹_›

theorem filter_same_keys_0' (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    (∀ k, (get? m1 k).isSome → (get? m2 k).isSome) →
    ∀ k, (get? (filter (fun k _ => decide (P k)) m1) k).isSome →
         (get? (filter (fun k _ => decide (P k)) m2) k).isSome := by
  intro h k
  simp only [mapLookup_filter_key]
  split
  · exact h k
  · simp

theorem filter_same_keys_1' (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    (∀ k, (get? (filter (fun k _ => decide (P k)) m1) k).isSome →
          (get? (filter (fun k _ => decide (P k)) m2) k).isSome) →
    (∀ k, (get? (filter (fun k _ => decide (¬ P k)) m1) k).isSome →
          (get? (filter (fun k _ => decide (¬ P k)) m2) k).isSome) →
    ∀ k, (get? m1 k).isSome → (get? m2 k).isSome := by
  intro h1 h2 k
  have h1 := h1 k; have h2 := h2 k
  simp only [mapLookup_filter_key] at h1 h2
  by_cases hP : P k <;> simp_all

/-- The domain of a key-filtered map is the filtered domain. -/
theorem filter_dom (P : K → Prop) [DecidablePred P] (m : M A) :
    dom (filter (fun k _ => decide (P k)) m) = fun k => P k ∧ dom m k := by
  funext k
  simp only [dom, mapLookup_filter_key]
  by_cases hP : P k <;> simp [hP]

theorem filter_same_keys_0 (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    (∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) →
    ∀ k, (get? (filter (fun k _ => decide (P k)) m1) k).isSome ↔
         (get? (filter (fun k _ => decide (P k)) m2) k).isSome := by
  intro h k
  exact ⟨filter_same_keys_0' m1 m2 P (fun k => (h k).1) k,
    filter_same_keys_0' m2 m1 P (fun k => (h k).2) k⟩

theorem filter_same_keys_1 (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    (∀ k, (get? (filter (fun k _ => decide (P k)) m1) k).isSome ↔
          (get? (filter (fun k _ => decide (P k)) m2) k).isSome) →
    (∀ k, (get? (filter (fun k _ => decide (¬ P k)) m1) k).isSome ↔
          (get? (filter (fun k _ => decide (¬ P k)) m2) k).isSome) →
    ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome := by
  intro h1 h2 k
  exact ⟨filter_same_keys_1' m1 m2 P (fun k => (h1 k).1) (fun k => (h2 k).1) k,
    filter_same_keys_1' m2 m1 P (fun k => (h1 k).2) (fun k => (h2 k).2) k⟩

theorem dom_filter_eq (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    dom m1 = dom m2 →
    dom (filter (fun k _ => decide (P k)) m1) = dom (filter (fun k _ => decide (P k)) m2) := by
  intro h
  rw [filter_dom, filter_dom, h]

/-- A map is the union of its filter and the complementary filter. -/
theorem map_filter_union_complement (φ : K → A → Bool) (m : M A) :
    filter φ m ∪ filter (fun k v => !φ k v) m = m := by
  apply equiv_iff_eq.mp
  intro k
  rw [get?_union, get?_filter, get?_filter]
  cases get? m k with
  | none => rfl
  | some v => cases h : φ k v <;> simp [h]

theorem map_disjoint_filter_complement (φ : K → A → Bool) (m : M A) :
    filter φ m ##ₘ filter (fun k v => !φ k v) m := by
  intro k
  rw [get?_filter, get?_filter]
  cases get? m k with
  | none => simp
  | some v => cases φ k v <;> simp

end filter

/-! ## `map_zip_with` and `mapZip` -/

section mapZip

variable {K : Type _} {M : Type u → Type _} [LawfulFiniteMap M K] [DecidableEq K]
variable {A B C : Type u}

theorem mapZip_with_empty_l (f : A → B → C) (m2 : M B) :
    zipWith f (∅ : M A) m2 = (∅ : M C) := by
  apply equiv_iff_eq.mp; intro k
  simp [get?_zipWith, get?_empty]

theorem mapZip_with_empty_r (f : A → B → C) (m1 : M A) :
    zipWith f m1 (∅ : M B) = (∅ : M C) := by
  apply equiv_iff_eq.mp; intro k
  simp only [get?_zipWith, get?_empty]
  cases get? m1 k <;> rfl

/-- Zip of two maps, in the form used by iris-lean's `[∗map] k ↦ x1;x2 ∈ m1;m2, _`
(`PartialMap.zip` itself has universe-polymorphism issues). -/
abbrev mapZip (m1 : M A) (m2 : M B) : M (A × B) := zipWith (fun (x : A) (y : B) => (x, y)) m1 m2

theorem mapZip_empty_l (m2 : M B) : mapZip (∅ : M A) m2 = ∅ := mapZip_with_empty_l _ m2

theorem mapZip_empty_r (m1 : M A) : mapZip m1 (∅ : M B) = ∅ := mapZip_with_empty_r _ m1

theorem mapZip_insert (m1 : M A) (m2 : M B) (i : K) (v1 : A) (v2 : B) :
    mapZip (insert m1 i v1) (insert m2 i v2) = insert (mapZip m1 m2) i (v1, v2) :=
  zipWith_insert

theorem mapZip_lookup_none_1 (m1 : M A) (m2 : M B) (i : K) :
    get? m1 i = none → get? (mapZip m1 m2) i = none := by
  intro h; rw [get?_zipWith, h]; rfl

theorem mapZip_lookup_none_2 (m1 : M A) (m2 : M B) (i : K) :
    get? m2 i = none → get? (mapZip m1 m2) i = none := by
  intro h; rw [get?_zipWith, h]; cases get? m1 i <;> rfl

theorem mapZip_lookup_some (m1 : M A) (m2 : M B) (i : K) (v1 : A) (v2 : B) :
    get? m1 i = some v1 → get? m2 i = some v2 → get? (mapZip m1 m2) i = some (v1, v2) := by
  intro h1 h2; rw [get?_zipWith, h1, h2]; rfl

theorem mapZip_filter (m1 : M A) (m2 : M B) (P : K → Prop) [DecidablePred P] :
    mapZip (filter (fun k _ => decide (P k)) m1) (filter (fun k _ => decide (P k)) m2) =
    filter (fun k _ => decide (P k)) (mapZip m1 m2) := by
  apply equiv_iff_eq.mp; intro k
  simp only [get?_zipWith, mapLookup_filter_key]
  split <;> rfl

end mapZip

/-! ## `big_sepM` -/

section bi

variable {PROP : Type _} [BI PROP] [BIAffine PROP]
variable {K : Type _} {M : Type u → Type _} [LawfulFiniteMap M K] [DecidableEq K]

section map

variable {A : Type u}

theorem big_sepS_exists_sepM {S : Type _} [LawfulFiniteSet S K] (Φ : K → A → PROP) (s : S) :
    ([∗set] k ∈ s, ∃ v, Φ k v) ⊢
      ∃ m : M A, ⌜FiniteMap.dom_set m = s⌝ ∗ [∗map] k ↦ v ∈ m, Φ k v := by
  induction s using FiniteSet.set_ind with
  | hemp =>
    iintro _
    iexists (∅ : M A)
    isplitr
    · ipureintro
      ext k
      simp only [LawfulFiniteMap.mem_dom_set, get?_empty, Option.isSome_none]
      exact ⟨nofun, fun h => absurd h LawfulSet.mem_empty⟩
    · rw [bigSepM_empty.to_eq]; iempintro
  | hadd x s hnin ih =>
    rw [(bigSepS_insert hnin).to_eq]
    iintro ⟨⟨%v, HΦ⟩, Hs⟩
    icases ih $$ Hs with ⟨%m, %hdom, H⟩
    have hx : get? m x = none := by
      cases h : get? m x with
      | none => rfl
      | some _ =>
        exfalso; apply hnin; rw [← hdom]
        exact LawfulFiniteMap.mem_dom_set.mpr (by simp [h])
    iexists (insert m x v)
    isplitr
    · ipureintro
      ext k
      rw [LawfulFiniteMap.mem_dom_set, get?_insert, LawfulSet.mem_insert, ← hdom,
        LawfulFiniteMap.mem_dom_set]
      by_cases hk : x = k
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    · rw [(bigSepM_insert hx).to_eq]
      iframe

theorem big_sepM_mono_with_inv' (P : PROP) (Φ Ψ : K → A → PROP) (m : M A) :
    (∀ k x, get? m k = some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗map] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗map] k ↦ x ∈ m, Ψ k x := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
    intro _
    rw [bigSepM_empty.to_eq, bigSepM_empty.to_eq]
  | hins i x m hi IH =>
    intro h
    rw [(bigSepM_insert hi).to_eq, (bigSepM_insert hi).to_eq]
    have IH' := IH fun k x' hk => h k x' (by
      rw [get?_insert_ne (fun hik => by subst hik; simp_all)]; exact hk)
    iintro ⟨HP, Hi, H⟩
    icases (h i x (get?_insert_eq rfl)) $$ [$HP $Hi] with ⟨HP, Hi⟩
    icases IH' $$ [$HP $H] with ⟨HP, H⟩
    iframe

theorem big_sepM_mono_with_inv (P : PROP) (Φ Ψ : K → A → PROP) (m : M A) :
    (∀ k x, get? m k = some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ⊢ ([∗map] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗map] k ↦ x ∈ m, Ψ k x := by
  intro h
  exact wand_intro (big_sepM_mono_with_inv' P Φ Ψ m h)

theorem big_sepM_mono_wand (Φ Ψ : K → A → PROP) (m : M A) (I : PROP) :
    □ (∀ k x, ⌜get? m k = some x⌝ -∗ I ∗ Φ k x -∗ I ∗ Ψ k x) ⊢
    I ∗ ([∗map] k ↦ x ∈ m, Φ k x) -∗
    I ∗ ([∗map] k ↦ x ∈ m, Ψ k x) := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
    rw [bigSepM_empty.to_eq, bigSepM_empty.to_eq]
    iintro _ H
    iexact H
  | hins i x m hi IH =>
    rw [(bigSepM_insert hi).to_eq, (bigSepM_insert hi).to_eq]
    iintro #Hw ⟨HI, Hi, H⟩
    icases Hw $$ %i %x %(get?_insert_eq rfl) [$HI $Hi] with ⟨HI, Hi⟩
    icases IH $$ [#] [$HI $H] with ⟨HI, H⟩
    · iintro !> %k %x' %hk ⟨HI, Hk⟩
      have hne : i ≠ k := fun hik => by subst hik; simp_all
      iapply Hw $$ %k %x' %(by rw [get?_insert_ne hne]; exact hk) [$HI $Hk]
    iframe

theorem big_sepM_mono_fupd [BIFUpdate PROP] (Φ Ψ : K → A → PROP) (m : M A) (I : PROP)
    (E : CoPset) :
    □ (∀ k x, ⌜get? m k = some x⌝ -∗ I ∗ Φ k x ={E}=∗ I ∗ Ψ k x) ⊢
    I ∗ ([∗map] k ↦ x ∈ m, Φ k x) ={E}=∗
    I ∗ ([∗map] k ↦ x ∈ m, Ψ k x) := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
    rw [bigSepM_empty.to_eq, bigSepM_empty.to_eq]
    iintro _ H
    imodintro
    iexact H
  | hins i x m hi IH =>
    rw [(bigSepM_insert hi).to_eq, (bigSepM_insert hi).to_eq]
    iintro #Hw ⟨HI, Hi, H⟩
    imod Hw $$ %i %x %(get?_insert_eq rfl) [$HI $Hi] with ⟨HI, Hi⟩
    imod IH $$ [#] [$HI $H] with ⟨HI, H⟩
    · iintro !> %k %x' %hk ⟨HI, Hk⟩
      have hne : i ≠ k := fun hik => by subst hik; simp_all
      iapply Hw $$ %k %x' %(by rw [get?_insert_ne hne]; exact hk) [$HI $Hk]
    imodintro
    iframe

theorem big_sepM_mono_bupd [BIUpdate PROP] (Φ Ψ : K → A → PROP) (m : M A) (I : PROP) :
    □ (∀ k x, ⌜get? m k = some x⌝ -∗ I ∗ Φ k x ==∗ I ∗ Ψ k x) ⊢
    I ∗ ([∗map] k ↦ x ∈ m, Φ k x) ==∗
    I ∗ ([∗map] k ↦ x ∈ m, Ψ k x) := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
    rw [bigSepM_empty.to_eq, bigSepM_empty.to_eq]
    iintro _ H
    imodintro
    iexact H
  | hins i x m hi IH =>
    rw [(bigSepM_insert hi).to_eq, (bigSepM_insert hi).to_eq]
    iintro #Hw ⟨HI, Hi, H⟩
    imod Hw $$ %i %x %(get?_insert_eq rfl) [$HI $Hi] with ⟨HI, Hi⟩
    imod IH $$ [#] [$HI $H] with ⟨HI, H⟩
    · iintro !> %k %x' %hk ⟨HI, Hk⟩
      have hne : i ≠ k := fun hik => by subst hik; simp_all
      iapply Hw $$ %k %x' %(by rw [get?_insert_ne hne]; exact hk) [$HI $Hk]
    imodintro
    iframe

theorem big_sepM_impl_subseteq (m m' : M A) :
    ⊢@{PROP} ([∗map] k ↦ v ∈ m, ⌜get? m' k = some v⌝) -∗ ⌜m ⊆ m'⌝ :=
  entails_wand <| bigSepM_pure_intro.trans <| pure_mono fun h k v hk => h k v hk

theorem big_sepM_lookup_holds (m : M A) :
    ⊢@{PROP} [∗map] k ↦ v ∈ m, ⌜get? m k = some v⌝ :=
  (pure_intro (fun _ _ h => h : PartialMap.all (fun k v => get? m k = some v) m)).trans
    bigSepM_pure.2

theorem big_sepM_subseteq_diff (Φ : K → A → PROP) (m1 m2 : M A) :
    m2 ⊆ m1 →
    ([∗map] k ↦ x ∈ m1, Φ k x) ⊢
      ([∗map] k ↦ x ∈ m2, Φ k x) ∗ ([∗map] k ↦ x ∈ m1 \ m2, Φ k x) := by
  intro h
  have := (bigSepM_union (Φ := Φ) (disjoint_difference_right (m₁ := m1) (m₂ := m2))).1
  rwa [union_difference_cancel h] at this

theorem big_sepM_subseteq_acc (Φ : K → A → PROP) (m1 m2 : M A) :
    m2 ⊆ m1 →
    ([∗map] k ↦ x ∈ m1, Φ k x) ⊢
      ([∗map] k ↦ x ∈ m2, Φ k x) ∗
      (([∗map] k ↦ x ∈ m2, Φ k x) -∗ [∗map] k ↦ x ∈ m1, Φ k x) := by
  intro h
  refine (big_sepM_subseteq_diff Φ m1 m2 h).trans (sep_mono_right (wand_intro ?_))
  have := (bigSepM_union (Φ := Φ) (disjoint_difference_right (m₁ := m1) (m₂ := m2))).2
  rw [union_difference_cancel h] at this
  exact sep_comm.1.trans this

theorem big_sepM_filter_split (Φ : K → A → PROP) (P : K → A → Prop) [∀ k v, Decidable (P k v)]
    (m : M A) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢
      ([∗map] k ↦ x ∈ filter (fun k v => decide (P k v)) m, Φ k x) ∗
      ([∗map] k ↦ x ∈ filter (fun k v => decide (¬ P k v)) m, Φ k x) := by
  have hc : (fun k v => decide (¬ P k v)) = (fun k v => !decide (P k v)) := by
    funext k v; simp
  rw [hc]
  conv => lhs; rw [← map_filter_union_complement (fun k v => decide (P k v)) m]
  exact bigSepM_union (map_disjoint_filter_complement _ m)

theorem big_sepM_mono_gen_Q {B : Type u} (Q : PROP) (Φ : K → A → PROP) (Ψ : K → B → PROP)
    (m1 : M A) (m2 : M B) :
    ⊢ ⌜∀ k, get? m1 k = none → get? m2 k = none⌝ -∗
      □ (∀ k x1, ⌜get? m1 k = some x1⌝ -∗ (Q ∗ Φ k x1) -∗
          ∃ x2, ⌜get? m2 k = some x2⌝ ∗ (Q ∗ Ψ k x2)) -∗
      (Q ∗ [∗map] k ↦ x ∈ m1, Φ k x) -∗
      (Q ∗ [∗map] k ↦ x ∈ m2, Ψ k x) := by
  induction m1 using LawfulFiniteMap.induction_on generalizing m2 with
  | hemp =>
    iintro %hnone #_ ⟨HQ, _⟩
    have : m2 = ∅ := eq_empty_iff.mpr fun k => hnone k (get?_empty k)
    subst this
    rw [bigSepM_empty.to_eq]
    iframe
    rw [bigSepM_empty.to_eq]
    iempintro
  | hins i x m hi IH =>
    iintro %hnone #Hs ⟨HQ, Hm⟩
    icases (bigSepM_insert hi).1 $$ Hm with ⟨Hi, Hm⟩
    icases Hs $$ %i %x %(get?_insert_eq rfl) [$HQ $Hi] with ⟨%x2, %hx2, HQ, Hi⟩
    have hnone' : ∀ k, get? m k = none → get? (delete m2 i) k = none := by
      intro k hk
      by_cases hik : i = k
      · exact get?_delete_eq hik
      · rw [get?_delete_ne hik]
        exact hnone k (by rw [get?_insert_ne hik]; exact hk)
    icases IH (delete m2 i) $$ %hnone' [#] [$HQ $Hm] with ⟨HQ, Hm⟩
    · iintro !> %k %x1 %hk H
      have hne : i ≠ k := fun hik => by subst hik; simp_all
      icases Hs $$ %k %x1 %(by rw [get?_insert_ne hne]; exact hk) H with ⟨%x2', %hx2', H⟩
      iexists x2'
      iframe
      ipureintro
      rw [get?_delete_ne hne]; exact hx2'
    rw [(bigSepM_delete hx2).to_eq]
    iframe

theorem big_sepM_mono_gen {B : Type u} (Φ : K → A → PROP) (Ψ : K → B → PROP)
    (m1 : M A) (m2 : M B) :
    ⊢ ⌜∀ k, get? m1 k = none → get? m2 k = none⌝ -∗
      □ (∀ k x1, ⌜get? m1 k = some x1⌝ -∗ Φ k x1 -∗
          ∃ x2, ⌜get? m2 k = some x2⌝ ∗ Ψ k x2) -∗
      ([∗map] k ↦ x ∈ m1, Φ k x) -∗
      ([∗map] k ↦ x ∈ m2, Ψ k x) := by
  iintro %hnone #Hs Hm
  icases (big_sepM_mono_gen_Q emp Φ Ψ m1 m2) $$ %hnone [#] [$Hm] with ⟨_, H⟩
  · iintro !> %k %x1 %hk ⟨_, H⟩
    icases Hs $$ %k %x1 %hk H with ⟨%x2, %hx2, H⟩
    iexists x2
    iframe
    ipureintro; exact hx2
  iexact H

theorem big_sepM_mono_dom_Q {B : Type u} (Q : PROP) (Φ : K → A → PROP) (Ψ : K → B → PROP)
    (m1 : M A) (m2 : M B) :
    dom m1 = dom m2 →
    ⊢ □ (∀ k x1, ⌜get? m1 k = some x1⌝ -∗ (Q ∗ Φ k x1) -∗
          ∃ x2, ⌜get? m2 k = some x2⌝ ∗ (Q ∗ Ψ k x2)) -∗
      (Q ∗ [∗map] k ↦ x ∈ m1, Φ k x) -∗
      (Q ∗ [∗map] k ↦ x ∈ m2, Ψ k x) := by
  intro hdom
  iapply (big_sepM_mono_gen_Q Q Φ Ψ m1 m2)
  ipureintro
  intro k hk
  exact (map_dom_eq_none hdom).mp hk

theorem big_sepM_mono_dom {B : Type u} (Φ : K → A → PROP) (Ψ : K → B → PROP)
    (m1 : M A) (m2 : M B) :
    dom m1 = dom m2 →
    ⊢ □ (∀ k x1, ⌜get? m1 k = some x1⌝ -∗ Φ k x1 -∗
          ∃ x2, ⌜get? m2 k = some x2⌝ ∗ Ψ k x2) -∗
      ([∗map] k ↦ x ∈ m1, Φ k x) -∗
      ([∗map] k ↦ x ∈ m2, Ψ k x) := by
  intro hdom
  iapply (big_sepM_mono_gen Φ Ψ m1 m2)
  ipureintro
  intro k hk
  exact (map_dom_eq_none hdom).mp hk

end map

/-! ## `big_sepM2` -/

section map2

variable {A B : Type u}

theorem big_sepM2_lookup_l_some (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) (i : K) (x1 : A) :
    get? m1 i = some x1 →
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ⌜∃ x2, get? m2 i = some x2⌝ := by
  intro h
  refine bigSepM2_lookup_iff.trans (pure_mono fun hd => ?_)
  exact Option.isSome_iff_exists.mp ((hd i).mp (by simp [h]))

theorem big_sepM2_lookup_r_some (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) (i : K) (x2 : B) :
    get? m2 i = some x2 →
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ⌜∃ x1, get? m1 i = some x1⌝ := by
  intro h
  refine bigSepM2_lookup_iff.trans (pure_mono fun hd => ?_)
  exact Option.isSome_iff_exists.mp ((hd i).mpr (by simp [h]))

theorem big_sepM2_lookup_l_none (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) (i : K) :
    get? m1 i = none →
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ⌜get? m2 i = none⌝ := by
  intro h
  refine bigSepM2_lookup_iff.trans (pure_mono fun hd => ?_)
  have := hd i
  cases h2 : get? m2 i <;> simp_all

theorem big_sepM2_lookup_r_none (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) (i : K) :
    get? m2 i = none →
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ⌜get? m1 i = none⌝ := by
  intro h
  refine bigSepM2_lookup_iff.trans (pure_mono fun hd => ?_)
  have := hd i
  cases h1 : get? m1 i <;> simp_all

theorem big_sepM2_sepM_1 (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
      [∗map] k ↦ y1 ∈ m1, ∃ y2, ⌜get? m2 k = some y2⌝ ∗ Φ k y1 y2 := by
  induction m1 using LawfulFiniteMap.induction_on generalizing m2 with
  | hemp =>
    rw [bigSepM_empty.to_eq]
    iintro _
    iempintro
  | hins i x m hi IH =>
    iintro H
    ihave %hx2 := (big_sepM2_lookup_l_some Φ _ m2 i x (get?_insert_eq rfl)) $$ H
    obtain ⟨x2, hx2⟩ := hx2
    rw [(bigSepM2_delete (get?_insert_eq rfl) hx2).to_eq, delete_insert_cancel hi,
      (bigSepM_insert hi).to_eq]
    icases H with ⟨Hi, H⟩
    ihave H := IH (delete m2 i) $$ H
    isplitl [Hi]
    · iexists x2
      iframe
      ipureintro; exact hx2
    · iapply (bigSepM_mono (fun {k y1} hk => ?_)) $$ H
      iintro ⟨%y2, %hy2, H⟩
      iexists y2
      iframe
      ipureintro
      have hne : i ≠ k := fun hik => by subst hik; simp_all
      rw [get?_delete_ne hne] at hy2; exact hy2

theorem big_sepM2_sepM_2 (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
      [∗map] k ↦ y2 ∈ m2, ∃ y1, ⌜get? m1 k = some y1⌝ ∗ Φ k y1 y2 :=
  bigSepM2_flip.2.trans (big_sepM2_sepM_1 (fun k y2 y1 => Φ k y1 y2) m2 m1)

theorem big_sepM_sepM2_exists (Φ : K → A → B → PROP) (m1 : M A) :
    ([∗map] k ↦ y1 ∈ m1, ∃ y2, Φ k y1 y2) ⊢
      ∃ m2 : M B, [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2 := by
  induction m1 using LawfulFiniteMap.induction_on with
  | hemp =>
    iintro _
    iexists (∅ : M B)
    rw [(bigSepM2_empty Φ).to_eq]
    iempintro
  | hins i x m hi IH =>
    rw [(bigSepM_insert hi).to_eq]
    iintro ⟨⟨%y2, Hi⟩, Hm⟩
    icases IH $$ Hm with ⟨%m2, Hm⟩
    ihave %hm2 := (big_sepM2_lookup_l_none Φ m m2 i hi) $$ Hm
    iexists (insert m2 i y2)
    rw [(bigSepM2_insert hi hm2).to_eq]
    iframe

theorem big_sepM_sepM2_merge (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : M A) (m2 : M B) :
    dom m1 = dom m2 →
    ([∗map] k ↦ y1 ∈ m1, Φ k y1) ∗ ([∗map] k ↦ y2 ∈ m2, Ψ k y2) ⊢
      [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 ∗ Ψ k y2 := by
  intro hdom
  refine (bigSepM2_sepM fun k => ?_).2
  rw [map_dom_eq_iff.mp hdom k]

theorem big_sepM_sepM2_merge_ex (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    dom m1 = dom m2 →
    ([∗map] k ↦ y1 ∈ m1, ∃ y2, ⌜get? m2 k = some y2⌝ ∗ Φ k y1 y2) ⊢
      [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2 := by
  intro hdom
  refine .trans ?_ ((big_sepM_sepM2_merge
    (fun k y1 => iprop(∃ y2, ⌜get? m2 k = some y2⌝ ∗ Φ k y1 y2)) (fun _ _ => (emp : PROP))
    m1 m2 hdom).trans ?_)
  · exact sep_emp.2.trans (sep_mono_right bigSepM_emp.2)
  · refine bigSepM2_mono fun {k y1 y2} _ hk2 => ?_
    iintro ⟨⟨%y0, %hy0, H⟩, _⟩
    rw [hk2] at hy0
    cases hy0
    iexact H

theorem big_sepM2_sepM_merge (Φ : K → A → B → PROP) (Ψ : K → A → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ∗ ([∗map] k ↦ y1 ∈ m1, Ψ k y1) ⊢
      [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 := by
  iintro ⟨H2, H⟩
  ihave %hdom := (bigSepM2_dom Φ m1 m2) $$ H2
  ihave H := (big_sepM_sepM2_merge Ψ (fun _ _ => (emp : PROP)) m1 m2 hdom) $$ [$H]
  · iapply bigSepM_emp.2
    iempintro
  iapply bigSepM2_sep_eqv.2
  iframe H2
  iapply (bigSepM2_mono fun {k y1 y2} _ _ => sep_elim_left) $$ H

theorem big_sepM2_filter (Φ : K → A → B → PROP) (P : K → Prop) [DecidablePred P]
    (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢
      ([∗map] k ↦ y1;y2 ∈ filter (fun k _ => decide (P k)) m1;
          filter (fun k _ => decide (P k)) m2, Φ k y1 y2) ∗
      ([∗map] k ↦ y1;y2 ∈ filter (fun k _ => decide (¬ P k)) m1;
          filter (fun k _ => decide (¬ P k)) m2, Φ k y1 y2) := by
  have hz := mapZip_filter m1 m2 P
  have hz' := mapZip_filter m1 m2 (fun k => ¬ P k)
  have hsplit := big_sepM_filter_split (fun k (xy : A × B) => Φ k xy.1 xy.2) (fun k _ => P k)
    (zipWith (fun (x : A) (y : B) => (x, y)) m1 m2)
  rw [← hz, ← hz'] at hsplit
  constructor
  · refine bigSepM2_alt.1.trans ?_
    refine pure_elim_left fun hdom => ?_
    refine hsplit.1.trans (sep_mono ?_ ?_)
    · exact (and_intro (pure_intro (dom_filter_eq m1 m2 P hdom)) .rfl).trans bigSepM2_alt.2
    · exact (and_intro (pure_intro (dom_filter_eq m1 m2 (fun k => ¬ P k) hdom)) .rfl).trans
        bigSepM2_alt.2
  · iintro ⟨H1, H2⟩
    icases bigSepM2_alt.1 $$ H1 with ⟨%hd1, H1⟩
    icases bigSepM2_alt.1 $$ H2 with ⟨%hd2, H2⟩
    iapply bigSepM2_alt.2
    isplit
    · ipureintro
      rw [filter_dom, filter_dom] at hd1
      rw [filter_dom (fun k => ¬ P k), filter_dom (fun k => ¬ P k)] at hd2
      funext k
      have e1 := congrFun hd1 k
      have e2 := congrFun hd2 k
      by_cases hP : P k <;> simp_all
    · iapply hsplit.2
      iframe

theorem big_sepM2_insert_left_inv (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) (k : K) (a : A) :
    get? m1 k = none →
    ([∗map] k ↦ y1;y2 ∈ insert m1 k a;m2, Φ k y1 y2) ⊢
      ∃ b, ⌜get? m2 k = some b⌝ ∗ Φ k a b ∗ [∗map] k ↦ y1;y2 ∈ m1;delete m2 k, Φ k y1 y2 := by
  intro hk
  iintro H
  ihave %hb := (big_sepM2_lookup_l_some Φ _ m2 k a (get?_insert_eq rfl)) $$ H
  obtain ⟨b, hb⟩ := hb
  rw [(bigSepM2_delete (get?_insert_eq rfl) hb).to_eq, delete_insert_cancel hk]
  iexists b
  iframe
  ipureintro; exact hb

end map2

end bi

/-! ## Currying of `gmap`s indexed by pairs -/

section map_uncurry

noncomputable section

open Classical

variable {A B : Type _} [DecidableEq A] [DecidableEq B] {T : Type _}

/-- The inner map of `gmapCurry m` at `a` (possibly empty). -/
def gmapCurryInner (m : GMap (A × B) T) (a : A) : GMap B T :=
  ⟨fun b => m !! (a, b), by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l.map Prod.snd, fun b h => List.mem_map.mpr ⟨(a, b), hl _ h, rfl⟩⟩⟩

/-- Currying of a map with pair keys (stdpp's `map_curry`): only keys with a nonempty inner map
are present. -/
def gmapCurry (m : GMap (A × B) T) : GMap A (GMap B T) :=
  ⟨fun a => if ∃ b, (m !! (a, b)).isSome then some (gmapCurryInner m a) else none, by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l.map Prod.fst, fun a h => ?_⟩
    split at h
    · rename_i hex
      obtain ⟨b, hb⟩ := hex
      exact List.mem_map.mpr ⟨(a, b), hl _ hb, rfl⟩
    · simp at h⟩

theorem gmapCurry_lookup_iff (m : GMap (A × B) T) (a : A) :
    gmapCurry m !! a =
      if ∃ b, (m !! (a, b)).isSome then some (gmapCurryInner m a) else none := by
  rfl

theorem gmapCurry_insert (m : GMap (A × B) T) (k : A × B) (v : T) :
    m !! k = none →
    gmapCurry (<[k := v]> m) =
      <[k.1 := <[k.2 := v]> ((gmapCurry m !! k.1).getD ∅)]> (gmapCurry m) := by
  intro _
  obtain ⟨a, b⟩ := k
  apply GMap.ext; intro a'
  rw [gmapCurry_lookup_iff, GMap.lookup_insert_eq_iff]
  by_cases ha : a = a'
  · subst ha
    rw [ite_eq_left rfl, ite_eq_left (⟨b, by simp⟩ : ∃ b', _)]
    congr 1
    apply GMap.ext; intro b'
    simp only [gmapCurryInner, GMap.lookup_mk, GMap.lookup_insert_eq_iff, Prod.mk.injEq,
      true_and]
    by_cases hb : b = b'
    · simp [hb]
    · rw [ite_eq_right hb, ite_eq_right hb, gmapCurry_lookup_iff]
      split
      · rfl
      · rename_i hnex
        cases h : m !! (a, b')
        · rfl
        · exact absurd ⟨b', by simp [h]⟩ hnex
  · rw [ite_eq_right ha, gmapCurry_lookup_iff]
    have hl : ∀ b', (<[(a, b) := v]> m) !! (a', b') = m !! (a', b') := by
      intro b'; simp [ha]
    have hi : gmapCurryInner (<[(a, b) := v]> m) a' = gmapCurryInner m a' := by
      apply GMap.ext; intro b'; exact hl b'
    simp only [hl, hi]

theorem gmapCurry_insert_delete (m : GMap (A × B) T) (k : A × B) (v : T) :
    m !! k = none →
    gmapCurry (<[k := v]> m) =
      <[k.1 := <[k.2 := v]> ((gmapCurry m !! k.1).getD ∅)]> (GMap.delete k.1 (gmapCurry m)) := by
  intro h
  rw [gmapCurry_insert m k v h, GMap.insert_delete]

theorem gmapCurry_lookup_exists (m : GMap (A × B) T) (k : A × B) (v : T) :
    m !! k = some v →
    ∃ offmap, gmapCurry m !! k.1 = some offmap ∧ offmap !! k.2 = some v := by
  intro h
  classical
  refine ⟨gmapCurryInner m k.1, ?_, ?_⟩
  · rw [gmapCurry_lookup_iff, ite_eq_left (⟨k.2, by simp [h]⟩ : ∃ b, _)]
  · simpa [gmapCurryInner] using h

theorem gmapCurry_lookup (m : GMap (A × B) T) (k1 : A) (k2 : B) (offmap : GMap B T) :
    gmapCurry m !! k1 = some offmap →
    m !! (k1, k2) = offmap !! k2 := by
  classical
  rw [gmapCurry_lookup_iff]
  split
  · intro h; cases h; rfl
  · intro h; cases h

end

end map_uncurry

end Perennial
