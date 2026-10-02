/-
Port of `new/ghost/ghost_map.v` (a modified copy of Iris' `ghost_map`): a "ghost
map" (or "ghost heap") with a proposition controlling authoritative ownership of
the entire map, and a "points-to-like" proposition for (mutable, fractional, or
persistent read-only) ownership of individual elements.

Built on `own` (see `Perennial/Ghost/All.lean`): keys and values are stored as
their `Pos.Countable` encodings in `HeapView Pos (Agree (DiscreteO Pos)) (gmap Pos)`,
so `allG` suffices (Rocq's `ghost_mapG` class is not needed).
-/
import Perennial.Ghost.Own
import Perennial.Ghost.Countable

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode HeapView
open Iris.Std (PartialMap LawfulPartialMap)
open scoped Iris.Std.PartialMap

/-! ## Encoding maps -/

section encode
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- The stored value for `v`. -/
abbrev encV (v : V) : Agree (DiscreteO Pos) := toAgree (encodeO v)

theorem encV_inj {v1 v2 : V} (h : encV v1 = encV v2) : v1 = v2 :=
  encodeO_inj (Agree.toAgree_inj h)

/-- The map stored in the authoritative element: `encode k ↦ encV v` for `k ↦ v ∈ m`. -/
def encMap (m : gmap K V) : gmap Pos (Agree (DiscreteO Pos)) :=
  ⟨fun p => match (Pos.Countable.decode p : Option K) with
      | some k => if Pos.Countable.encode k = p then (m.lookup k).map encV else none
      | none => none,
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l.map Pos.Countable.encode, fun p h => ?_⟩
    split at h
    · rename_i k _
      split at h
      · rename_i he
        subst he
        exact List.mem_map_of_mem (hl k (by simpa using h))
      · simp at h
    · simp at h⟩

theorem encMap_lookup_encode (m : gmap K V) (k : K) :
    (encMap m).lookup (Pos.Countable.encode k) = (m.lookup k).map encV := by
  simp [encMap, Pos.Countable.decode_encode]

theorem encMap_lookup_not_enc (m : gmap K V) {p : Pos} (h : ∀ k : K, Pos.Countable.encode k ≠ p) :
    (encMap m).lookup p = none := by
  simp only [encMap]
  split
  · rename_i k _; simp [h k]
  · rfl

/-- Extensionality for statements about `encMap`: it suffices to check encoded keys,
provided both sides vanish elsewhere. -/
theorem encMap_ext {m1 m2 : gmap Pos (Agree (DiscreteO Pos))}
    (henc : ∀ k : K, m1.lookup (Pos.Countable.encode k) = m2.lookup (Pos.Countable.encode k))
    (hother : ∀ p, (∀ k : K, Pos.Countable.encode k ≠ p) → m1.lookup p = m2.lookup p) :
    m1 = m2 := by
  apply gmap.ext; intro p
  by_cases h : ∃ k : K, Pos.Countable.encode k = p
  · obtain ⟨k, rfl⟩ := h; exact henc k
  · exact hother p (fun k hk => h ⟨k, hk⟩)

theorem encMap_inj {m1 m2 : gmap K V} (h : encMap m1 = encMap m2) : m1 = m2 := by
  apply gmap.ext; intro k
  have := congrArg (fun m => m.lookup (Pos.Countable.encode k)) h
  simp only [encMap_lookup_encode] at this
  cases h1 : m1.lookup k <;> cases h2 : m2.lookup k <;> simp_all
  exact encV_inj this

theorem encMap_empty : encMap (∅ : gmap K V) = ∅ :=
  encMap_ext (K := K) (fun k => by rw [encMap_lookup_encode]; rfl)
    (fun p h => by rw [encMap_lookup_not_enc _ h]; rfl)

theorem encMap_insert (m : gmap K V) (k : K) (v : V) :
    encMap (m.insert k v) = (encMap m).insert (Pos.Countable.encode k) (encV v) := by
  refine encMap_ext (K := K) (fun k' => ?_) (fun p h => ?_)
  · rw [encMap_lookup_encode]
    by_cases hk : k = k'
    · subst hk; simp [gmap.insert]
    · have : Pos.Countable.encode k ≠ Pos.Countable.encode k' := fun e => hk (Pos.encode_inj e)
      simp [gmap.insert, hk, this, encMap_lookup_encode]
  · rw [encMap_lookup_not_enc _ h]
    simp [gmap.insert, h k, encMap_lookup_not_enc _ h]

theorem encMap_delete (m : gmap K V) (k : K) :
    encMap (m.delete k) = (encMap m).delete (Pos.Countable.encode k) := by
  refine encMap_ext (K := K) (fun k' => ?_) (fun p h => ?_)
  · rw [encMap_lookup_encode]
    by_cases hk : k = k'
    · subst hk; simp [gmap.delete]
    · have : Pos.Countable.encode k ≠ Pos.Countable.encode k' := fun e => hk (Pos.encode_inj e)
      simp [gmap.delete, hk, this, encMap_lookup_encode]
  · rw [encMap_lookup_not_enc _ h]
    simp [gmap.delete, h k, encMap_lookup_not_enc _ h]

end encode

/-! ## Bridging `gmap` operations and the iris-lean `PartialMap` interface -/

section gmap_helpers
variable {K V : Type} [DecidableEq K]

theorem gmap_get?_eq (m : gmap K V) (k : K) : PartialMap.get? m k = m.lookup k := rfl

theorem gmap_union_eq (m1 m2 : gmap K V) :
    m1 ∪ m2 = PartialMap.union m1 m2 := by
  apply gmap.ext; intro k
  show (m1.lookup k).or (m2.lookup k) = Option.merge _ (m1.lookup k) (m2.lookup k)
  cases m1.lookup k <;> cases m2.lookup k <;> rfl

theorem gmap_lookup_union (m1 m2 : gmap K V) (k : K) :
    (m1 ∪ m2).lookup k = (m1.lookup k).or (m2.lookup k) := rfl

theorem gmap_lookup_difference (m1 m2 : gmap K V) (k : K) :
    (m1 \ m2).lookup k = if (m2.lookup k).isSome then none else m1.lookup k :=
  rfl

theorem gmap_disjoint_insert_left_iff {m₁ m₂ : gmap K V} {i : K} {x : V}
    (hi : m₁.lookup i = none) :
    gmap.disjoint (m₁.insert i x) m₂ ↔ m₂.lookup i = none ∧ gmap.disjoint m₁ m₂ := by
  constructor
  · intro hd
    refine ⟨?_, fun k h1 h2 => ?_⟩
    · cases h : m₂.lookup i with
      | none => rfl
      | some _ => exact (hd i (by simp [gmap.insert]) (by simp [h])).elim
    · by_cases hik : i = k
      · subst hik; simp [hi] at h1
      · exact hd k (by simpa [gmap.insert, hik] using h1) h2
  · rintro ⟨h2, hd⟩ k h1 h3
    by_cases hik : i = k
    · subst hik; simp [h2] at h3
    · exact hd k (by simpa [gmap.insert, hik] using h1) h3

end gmap_helpers

/-! ## Definitions -/

section definitions
variable {GF : BundledGFunctors} [allG GF]
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- Authoritative ownership (fraction `q`) of the whole map `m`. -/
def ghost_map_auth (γ : GName) (q : Qp) (m : gmap K V) : IProp GF :=
  own γ (HeapView.Auth (H := gmap Pos) (DFrac.own q) (encMap m))

/-- Ownership of the entry `k ↦ v`, with discardable fraction `dq`. -/
def ghost_map_elem (γ : GName) (k : K) (dq : DFrac) (v : V) : IProp GF :=
  own γ (HeapView.Frag (H := gmap Pos) (Pos.Countable.encode k) dq (encV v))

end definitions

/-- `k ↪[γ]{dq} v` (Rocq `k ↪[γ]{dq} v`). -/
notation:50 k:51 " ↪[" γ "]{" dq "} " v:51 => ghost_map_elem γ k dq v
/-- `k ↪[γ]{# q} v`. -/
notation:50 k:51 " ↪[" γ "]{#" q "} " v:51 => ghost_map_elem γ k (DFrac.own q) v
/-- `k ↪[γ]□ v`: persistent read-only ownership. -/
notation:50 k:51 " ↪[" γ "]□ " v:51 => ghost_map_elem γ k DFrac.discard v
/-- `k ↪[γ] v`: full ownership. -/
notation:50 k:51 " ↪[" γ "] " v:51 => ghost_map_elem γ k (DFrac.own 1) v

section lemmas
variable {GF : BundledGFunctors} [allG GF]
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-! ### Lemmas about the map elements -/

instance ghost_map_elem_timeless (k : K) (γ : GName) (dq : DFrac) (v : V) :
    Timeless (k ↪[γ]{dq} v : IProp GF) := by
  unfold ghost_map_elem; infer_instance

instance ghost_map_elem_persistent (k : K) (γ : GName) (v : V) :
    Persistent (k ↪[γ]□ v : IProp GF) := by
  unfold ghost_map_elem; infer_instance

instance ghost_map_elem_fractional (k : K) (γ : GName) (v : V) :
    Fractional (fun q => (k ↪[γ]{#q} v : IProp GF)) where
  fractional p q := by
    unfold ghost_map_elem
    refine .trans ?_ (own_op γ _ _)
    refine BIBase.BiEntails.of_eq ?_
    refine .trans ?_ (congrArg (own γ) frag_add_op_eqv)
    rw [Agree.idemp]

instance ghost_map_elem_as_fractional (k : K) (γ : GName) (q : Qp) (v : V) :
    AsFractional (k ↪[γ]{#q} v : IProp GF) ioΦ (fun q => k ↪[γ]{#q} v) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ghost_map_elem_fractional k γ v

theorem ghost_map_elem_valid (k : K) (γ : GName) (dq : DFrac) (v : V) :
    ⊢ (k ↪[γ]{dq} v : IProp GF) -∗ ⌜✓ dq⌝ := by
  unfold ghost_map_elem
  iintro H
  iapply (own_valid γ _).trans ?_ $$ H
  iintro %h
  ipureintro
  exact (frag_valid_iff.mp h).1

theorem ghost_map_elem_valid_2 (k : K) (γ : GName) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ (k ↪[γ]{dq1} v1 : IProp GF) -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := by
  unfold ghost_map_elem
  iintro H1 H2
  icombine H1 H2 gives %H
  obtain ⟨vdq, va⟩ := frag_op_valid_iff.mp H
  ipureintro
  exact ⟨vdq, encodeO_inj (toAgree_op_valid_iff_eq.mp va)⟩

theorem ghost_map_elem_agree (k : K) (γ : GName) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ (k ↪[γ]{dq1} v1 : IProp GF) -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝ := by
  iintro H1 H2
  ihave ⟨-, $⟩ := ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 $$ H1 H2

instance ghost_map_elem_combine_gives (γ : GName) (k : K) (v1 : V) (dq1 : DFrac) (v2 : V)
    (dq2 : DFrac) :
    CombineSepGives (k ↪[γ]{dq1} v1 : IProp GF) (k ↪[γ]{dq2} v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 $$ H1 H2 with %H
    itrivial

theorem ghost_map_elem_combine (k : K) (γ : GName) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ (k ↪[γ]{dq1} v1 : IProp GF) -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 • dq2} v1 ∗ ⌜v1 = v2⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %⟨-, rfl⟩
  isplitl [H1 H2]
  · unfold ghost_map_elem
    have h : (Frag (H := gmap Pos) (Pos.Countable.encode k) (dq1 • dq2) (encV v1)) =
        (Frag (H := gmap Pos) (Pos.Countable.encode k) dq1 (encV v1) •
          Frag (H := gmap Pos) (Pos.Countable.encode k) dq2 (encV v1) : HeapView _ _ _) := by
      rw [← frag_op_eqv, Agree.idemp]
    rw [h]
    iapply (own_op γ _ _).2
    isplitl [H1]
    · iexact H1
    · iexact H2
  · ipureintro; rfl

/-- Higher cost than the `Fractional` instance, which kicks in for `#q`s. -/
instance (priority := default - 20) ghost_map_elem_combine_as (k : K) (γ : GName)
    (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepAs (k ↪[γ]{dq1} v1 : IProp GF) (k ↪[γ]{dq2} v2) (k ↪[γ]{dq1 • dq2} v1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icases ghost_map_elem_combine k γ dq1 dq2 v1 v2 $$ H1 H2 with ⟨H, -⟩
    iexact H

theorem ghost_map_elem_frac_ne (γ : GName) (k1 k2 : K) (dq1 dq2 : DFrac) (v1 v2 : V)
    (Hk : ¬ ✓ (dq1 • dq2)) :
    ⊢ (k1 ↪[γ]{dq1} v1 : IProp GF) -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝ := by
  iintro H1 H2
  iintro %Heq; subst Heq
  icombine H1 H2 gives %⟨H, -⟩
  exact (Hk H).elim

theorem ghost_map_elem_ne (γ : GName) (k1 k2 : K) (dq2 : DFrac) (v1 v2 : V) :
    ⊢ (k1 ↪[γ] v1 : IProp GF) -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝ := by
  iintro H G
  iapply ghost_map_elem_frac_ne γ k1 k2 _ dq2 v1 v2 ?_ $$ H G
  intro HContra
  exact absurd (DFrac.valid_own_op HContra) (by have : (1 : Qp).val = 1 := rfl; grind)

/-- Make an element read-only. -/
theorem ghost_map_elem_persist (k : K) (γ : GName) (dq : DFrac) (v : V) :
    ⊢ (k ↪[γ]{dq} v : IProp GF) ==∗ k ↪[γ]□ v := by
  unfold ghost_map_elem
  iintro H
  iapply own_update γ _ _ update_frag_discard $$ H

/-- Recover fractional ownership for read-only element. -/
theorem ghost_map_elem_unpersist (k : K) (γ : GName) (v : V) :
    ⊢ (k ↪[γ]□ v : IProp GF) ==∗ ∃ q, k ↪[γ]{#q} v := by
  unfold ghost_map_elem
  iintro H
  imod own_updateP _ γ _ update_frag_acquire $$ H with ⟨%a, %Heq, G⟩
  obtain ⟨q, rfl⟩ := Heq
  iexists q
  iexact G

/-! ### Lemmas about `ghost_map_auth` -/

instance ghost_map_auth_timeless (γ : GName) (q : Qp) (m : gmap K V) :
    Timeless (ghost_map_auth γ q m : IProp GF) := by
  unfold ghost_map_auth; infer_instance

instance ghost_map_auth_fractional (γ : GName) (m : gmap K V) :
    Fractional (fun q => (ghost_map_auth γ q m : IProp GF)) where
  fractional p q := by
    unfold ghost_map_auth
    refine .trans ?_ (own_op γ _ _)
    exact BIBase.BiEntails.of_eq (congrArg (own γ) (auth_dfrac_op_eqv (dp := .own p) (dq := .own q)))

instance ghost_map_auth_as_fractional (γ : GName) (q : Qp) (m : gmap K V) :
    AsFractional (ghost_map_auth γ q m : IProp GF) ioΦ (fun q => ghost_map_auth γ q m) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ghost_map_auth_fractional γ m

theorem ghost_map_auth_valid (γ : GName) (q : Qp) (m : gmap K V) :
    ⊢ (ghost_map_auth γ q m : IProp GF) -∗ ⌜q ≤ 1⌝ := by
  unfold ghost_map_auth
  iintro H
  iapply (own_valid γ _).trans ?_ $$ H
  iintro %h
  ipureintro
  exact auth_valid_iff.mp h

theorem ghost_map_auth_valid_2 (γ : GName) (q1 q2 : Qp) (m1 m2 : gmap K V) :
    ⊢ (ghost_map_auth γ q1 m1 : IProp GF) -∗ ghost_map_auth γ q2 m2 -∗ ⌜q1 + q2 ≤ 1 ∧ m1 = m2⌝ := by
  unfold ghost_map_auth
  iintro H1 H2
  icombine H1 H2 gives %G
  ipureintro
  have ⟨h₁, h₂⟩ := auth_op_auth_valid_iff.mp G
  exact ⟨h₁, encMap_inj h₂⟩

theorem ghost_map_auth_agree (γ : GName) (q1 q2 : Qp) (m1 m2 : gmap K V) :
    ⊢ (ghost_map_auth γ q1 m1 : IProp GF) -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝ := by
  iintro H1 H2
  ihave ⟨_, $⟩ := ghost_map_auth_valid_2 γ q1 q2 m1 m2 $$ H1 H2

/-! ### Lemmas about the interaction of `ghost_map_auth` with the elements -/

theorem ghost_map_lookup {γ : GName} {q : Qp} {m : gmap K V} {k : K} {dq : DFrac} {v : V} :
    ⊢ (ghost_map_auth γ q m : IProp GF) -∗ k ↪[γ]{dq} v -∗ ⌜m.lookup k = some v⌝ := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  icombine H1 H2 gives %G
  ipureintro
  have ⟨av', _, _, h_av', _, h⟩ := auth_op_frag_valid_total_discrete_iff G
  have h_av' : (encMap m).lookup (Pos.Countable.encode k) = some av' := h_av'
  rw [encMap_lookup_encode] at h_av'
  cases hm : m.lookup k with
  | none => simp [hm] at h_av'
  | some w =>
    simp only [hm, Option.map_some, Option.some.injEq] at h_av'
    subst h_av'
    exact congrArg some (encodeO_inj (Agree.toAgree_included.mp h)).symm

instance ghost_map_lookup_combine_gives_1 {γ : GName} {q : Qp} {m : gmap K V} {k : K}
    {dq : DFrac} {v : V} :
    CombineSepGives (ghost_map_auth γ q m : IProp GF) (k ↪[γ]{dq} v) iprop(⌜m.lookup k = some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ H G with %H
    itrivial

instance ghost_map_lookup_combine_gives_2 {γ : GName} {q : Qp} {m : gmap K V} {k : K}
    {dq : DFrac} {v : V} :
    CombineSepGives (k ↪[γ]{dq} v : IProp GF) (ghost_map_auth γ q m) iprop(⌜m.lookup k = some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ G H with %H
    itrivial

theorem ghost_map_insert {γ : GName} {m : gmap K V} (k : K) (v : V) (Hm : m.lookup k = none) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) ==∗ ghost_map_auth γ 1 (m.insert k v) ∗ k ↪[γ] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro H
  have hfresh : PartialMap.get? (encMap m) (Pos.Countable.encode k) = none := by
    show (encMap m).lookup _ = none
    rw [encMap_lookup_encode, Hm]; rfl
  imod own_update γ _ _ (update_one_alloc (dq := DFrac.own 1) hfresh DFrac.valid_own_one
    Agree.toAgree_valid) $$ H with H
  rw [encMap_insert]
  iapply (own_op γ _ _).1 $$ H

theorem ghost_map_insert_persist {γ : GName} {m : gmap K V} (k : K) (v : V)
    (Hm : m.lookup k = none) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) ==∗ ghost_map_auth γ 1 (m.insert k v) ∗ k ↪[γ]□ v := by
  iintro H
  imod ghost_map_insert k v Hm $$ H with ⟨$, G⟩
  iapply ghost_map_elem_persist $$ G

theorem ghost_map_delete {γ : GName} {m : gmap K V} {k : K} {v : V} :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (m.delete k) := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  rw [encMap_delete]
  iapply own_update_2 γ _ _ _ update_one_delete $$ H1 H2

theorem ghost_map_update {γ : GName} {m : gmap K V} {k : K} {v : V} (w : V) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) -∗ k ↪[γ] v ==∗
      ghost_map_auth γ 1 (m.insert k w) ∗ k ↪[γ] w := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  rw [encMap_insert]
  ieval (rewrite [← (own_op γ _ _).to_eq])
  iapply own_update_2 γ _ _ _ (update_replace Agree.toAgree_valid) $$ H1 H2

/-! ### Big-op versions of the above lemmas -/

private theorem union_empty_left' (m : gmap K V) : (∅ : gmap K V) ∪ m = m := by
  apply gmap.ext; intro k; rw [gmap_lookup_union]; rfl

private theorem union_empty_right' (m : gmap K V) : m ∪ (∅ : gmap K V) = m := by
  apply gmap.ext; intro k; rw [gmap_lookup_union]; cases m.lookup k <;> rfl

theorem ghost_map_lookup_big {γ : GName} {q : Qp} {m : gmap K V} {dq : DFrac} (m0 : gmap K V) :
    ⊢ (ghost_map_auth γ q m : IProp GF) -∗ ([∗map] k ↦ v ∈ m0, k ↪[γ]{dq} v) -∗ ⌜m0 ⊆ m⌝ := by
  show ⊢ _ -∗ _ -∗ ⌜∀ k v, m0.lookup k = some v → m.lookup k = some v⌝
  iintro H1 H2 %k %v %Heq
  iapply ghost_map_lookup $$ H1 [H2]
  iapply BigSepM.bigSepM_lookup (Φ := fun k v => (k ↪[γ]{dq} v : IProp GF)) Heq $$ H2

theorem ghost_map_insert_big {γ : GName} {m : gmap K V} (m' : gmap K V) (Hdisj : gmap.disjoint m' m) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) ==∗
      ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗map] k ↦ v ∈ m', k ↪[γ] v) := by
  revert Hdisj
  induction m' using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro _
    rw [union_empty_left', BigSepM.bigSepM_empty.to_eq]
    iintro H
    imodintro
    isplitl [H]
    · iexact H
    · itrivial
  | hins i x m'' hi IH =>
    intro Hdisj
    obtain ⟨hm, Hdisj'⟩ := (gmap_disjoint_insert_left_iff hi).mp Hdisj
    have hi' : m''.lookup i = none := hi
    have hm' : m.lookup i = none := hm
    have hu : (m'' ∪ m).lookup i = none := by rw [gmap_lookup_union, hi', hm']; rfl
    have heq : Std.PartialMap.insert m'' i x ∪ m = (m'' ∪ m).insert i x := by
      apply gmap.ext; intro k
      show (if i = k then some x else m''.lookup k).or (m.lookup k) =
        if i = k then some x else (m''.lookup k).or (m.lookup k)
      split <;> rfl
    rw [heq, (BigSepM.bigSepM_insert (Φ := fun k v => (k ↪[γ] v : IProp GF)) hi).to_eq]
    iintro H
    imod IH Hdisj' $$ H with ⟨H, Hs⟩
    imod ghost_map_insert i x hu $$ H with ⟨H, Hi⟩
    imodintro
    isplitl [H]
    · iexact H
    · isplitl [Hi]
      · iexact Hi
      · iexact Hs

theorem ghost_map_insert_persist_big {γ : GName} {m : gmap K V} (m' : gmap K V)
    (Hdisj : gmap.disjoint m' m) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) ==∗
      ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗map] k ↦ v ∈ m', k ↪[γ]□ v) := by
  iintro H
  imod ghost_map_insert_big m' Hdisj $$ H with ⟨$, H⟩
  iapply BigSepM.bigSepM_bupd
  iapply BigSepM.bigSepM_impl $$ H
  iintro !> %k %v %Heq H
  iapply ghost_map_elem_persist $$ H

theorem ghost_map_delete_big {γ : GName} {m : gmap K V} (m0 : gmap K V) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) -∗ ([∗map] k ↦ v ∈ m0, k ↪[γ] v) ==∗
      ghost_map_auth γ 1 (m \ m0) := by
  induction m0 using Std.LawfulFiniteMap.induction_on generalizing m with
  | hemp =>
    have : m \ (∅ : gmap K V) = m := by
      apply gmap.ext; intro k; rw [gmap_lookup_difference]; rfl
    rw [this]
    iintro H _
    iexact H
  | hins i x m0 hi IH =>
    have heq : Std.PartialMap.delete m i \ m0 = m \ Std.PartialMap.insert m0 i x := by
      apply gmap.ext; intro k
      rw [gmap_lookup_difference, gmap_lookup_difference]
      show (if (m0.lookup k).isSome then none else (if i = k then none else m.lookup k)) =
        if (if i = k then some x else m0.lookup k).isSome then none else m.lookup k
      by_cases h : i = k <;> simp [h]
    rw [← heq, (BigSepM.bigSepM_insert (Φ := fun k v => (k ↪[γ] v : IProp GF)) hi).to_eq]
    iintro H ⟨Hi, Hs⟩
    imod ghost_map_delete $$ H Hi with H
    iapply IH $$ H Hs

theorem ghost_map_update_big {γ : GName} {m : gmap K V} (m0 m1 : gmap K V)
    (Hdom : gmap.domSet m0 = gmap.domSet m1) :
    ⊢ (ghost_map_auth γ 1 m : IProp GF) -∗ ([∗map] k ↦ v ∈ m0, k ↪[γ] v) ==∗
      ghost_map_auth γ 1 (m1 ∪ m) ∗ ([∗map] k ↦ v ∈ m1, k ↪[γ] v) := by
  have hdom : ∀ k, (m0.lookup k).isSome = (m1.lookup k).isSome := fun k => by
    have := congrArg (fun m => m.lookup k) Hdom
    change (m0.lookup k).map (fun _ => ()) = (m1.lookup k).map (fun _ => ()) at this
    revert this; cases m0.lookup k <;> cases m1.lookup k <;> simp
  have Hdisj : gmap.disjoint m1 (m \ m0) := by
    intro k h1 h2
    rw [gmap_lookup_difference, hdom k, h1] at h2
    simp at h2
  have heq : m1 ∪ (m \ m0) = m1 ∪ m := by
    apply gmap.ext; intro k
    rw [gmap_lookup_union, gmap_lookup_union, gmap_lookup_difference, hdom k]
    cases m1.lookup k <;> rfl
  rw [← heq]
  iintro H Hs
  imod ghost_map_delete_big m0 $$ H Hs with H
  iapply ghost_map_insert_big m1 Hdisj $$ H

theorem ghost_map_alloc_strong (P : GName → Prop) (m : gmap K V) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (ghost_map_auth γ 1 m : IProp GF) ∗ ([∗map] k ↦ v ∈ m, k ↪[γ] v) := by
  have H' := fun γ => ghost_map_insert_big (GF := GF) (γ := γ) (m := (∅ : gmap K V)) m
    (fun _ _ h => by simp at h)
  simp only [union_empty_right'] at H'
  unfold ghost_map_auth at H' ⊢
  imod own_alloc_strong (GF := GF)
    (HeapView.Auth (H := gmap Pos) (DFrac.own 1) (encMap (∅ : gmap K V))) P HP auth_one_valid
    with ⟨%γ, %Hγ, H⟩
  imod H' γ $$ H with ⟨H, Hs⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact Hγ
  · isplitl [H]
    · iexact H
    · iexact Hs

theorem ghost_map_alloc_strong_empty (P : GName → Prop) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (ghost_map_auth γ 1 (∅ : gmap K V) : IProp GF) := by
  imod ghost_map_alloc_strong (GF := GF) P (∅ : gmap K V) HP with ⟨%γ, %Hγ, H, -⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact Hγ
  · iexact H

theorem ghost_map_alloc (m : gmap K V) :
    ⊢ |==> ∃ γ, (ghost_map_auth γ 1 m : IProp GF) ∗ ([∗map] k ↦ v ∈ m, k ↪[γ] v) := by
  imod ghost_map_alloc_strong (GF := GF) (fun _ => True) m PredInfinite.true with ⟨%γ, -, H, Hs⟩
  imodintro
  iexists γ
  isplitl [H]
  · iexact H
  · iexact Hs

theorem ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, (ghost_map_auth γ 1 (∅ : gmap K V) : IProp GF) := by
  imod ghost_map_alloc (GF := GF) (∅ : gmap K V) with ⟨%γ, H, -⟩
  imodintro
  iexists γ
  iexact H

end lemmas

end Perennial
