/-
Derived properties of `own` (see `Perennial/Ghost/All.lean`
for the design).
-/
import Perennial.Ghost.All

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode Iris.Std Iris.Algebra

section global
variable {GF : BundledGFunctors} [AllG GF]
variable {A : Type} [CMRA A] {e : Syntax.Cmra} [H : IsCmra (IProp GF) A e]

theorem own_mono (γ : GName) (a1 a2 : A) (h : a2 ≼ a1) : own γ a1 ⊢ own γ a2 := by
  obtain ⟨c, rfl⟩ := h
  exact (own_op γ a2 c).1.trans sep_elim_left

theorem own_valid_2 (γ : GName) (a1 a2 : A) : ⊢ own γ a1 -∗ own γ a2 -∗ ✓ (a1 • a2) :=
  entails_wand (wand_intro ((own_op γ a1 a2).2.trans (own_valid γ _)))

theorem own_valid_3 (γ : GName) (a1 a2 a3 : A) :
    ⊢ own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ ((a1 • a2) • a3) :=
  entails_wand (wand_intro (wand_intro ((sep_mono_left (own_op γ a1 a2).2).trans
    ((own_op γ _ a3).2.trans (own_valid γ _)))))

theorem own_valid_r (γ : GName) (a : A) : own γ a ⊢ own γ a ∗ ✓ a :=
  persistent_entails_left (own_valid γ a)

theorem own_valid_l (γ : GName) (a : A) : own γ a ⊢ ✓ a ∗ own γ a :=
  persistent_entails_right (own_valid γ a)

private theorem le_foldr_max : ∀ (l : List Nat) (k : Nat), k ∈ l → k ≤ l.foldr max 0
  | [], _, h => by simp at h
  | x :: xs, k, h => by
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max xs k h) (Nat.le_max_right _ _)

theorem pred_infinite_not_mem (G : List GName) : PredInfinite (· ∉ G) := fun xs =>
  ⟨(G ++ xs).foldr max 0 + 1, fun h => by
      have := le_foldr_max (G ++ xs) _ (List.mem_append_left _ h); omega,
   fun h => by
      have := le_foldr_max (G ++ xs) _ (List.mem_append_right _ h); omega⟩

theorem own_alloc_cofinite_dep (f : GName → A) (G : List GName) (Ha : ∀ γ, γ ∉ G → ✓ f γ) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ) :=
  own_alloc_strong_dep f (· ∉ G) (pred_infinite_not_mem G) Ha

theorem own_alloc_dep (f : GName → A) (Ha : ∀ γ, ✓ f γ) : ⊢ |==> ∃ γ, own γ (f γ) :=
  (own_alloc_cofinite_dep f [] fun γ _ => Ha γ).trans
    (bupd_mono (exists_mono fun _ => sep_elim_right))

theorem own_alloc_strong (a : A) (P : GName → Prop) (HP : PredInfinite P) (Ha : ✓ a) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a :=
  own_alloc_strong_dep (fun _ => a) P HP fun _ _ => Ha

theorem own_alloc_cofinite (a : A) (G : List GName) (Ha : ✓ a) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a :=
  own_alloc_cofinite_dep (fun _ => a) G fun _ _ => Ha

theorem own_alloc (a : A) (Ha : ✓ a) : ⊢ |==> ∃ γ, own γ a :=
  own_alloc_dep (fun _ => a) fun _ => Ha

theorem own_update (γ : GName) (a a' : A) (Hupd : a ~~> a') : own γ a ⊢ |==> own γ a' :=
  (own_updateP (a' = ·) γ a (UpdateP.of_update Hupd)).trans <| bupd_mono <|
    exists_elim fun _ => by iintro ⟨%h, H⟩; subst h; iexact H

theorem own_update_2 (γ : GName) (a1 a2 a' : A) (Hupd : a1 • a2 ~~> a') :
    ⊢ own γ a1 -∗ own γ a2 ==∗ own γ a' :=
  entails_wand (wand_intro ((own_op γ a1 a2).2.trans (own_update γ _ _ Hupd)))

theorem own_update_3 (γ : GName) (a1 a2 a3 a' : A) (Hupd : (a1 • a2) • a3 ~~> a') :
    ⊢ own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a' :=
  entails_wand (wand_intro (wand_intro ((sep_mono_left (own_op γ a1 a2).2).trans
    ((own_op γ _ a3).2.trans (own_update γ _ _ Hupd)))))

end global

/-! ## Big-op homomorphisms -/
section big_op_instances
variable {GF : BundledGFunctors} [AllG GF]
variable {A : Type} [UCMRA A] {e : Syntax.Cmra} [H : IsCmra (IProp GF) A e]

instance own_cmra_sep_homomorphism (γ : GName) :
    Algebra.WeakMonoidHomomorphism (CMRA.op (α := A)) sep
      UCMRA.unit iprop(emp) BiEntails (own (GF := GF) γ) where
  rel_refl := .rfl
  rel_trans := .trans
  op_proper aa' bb' := sep_congr aa' bb'
  map_ne := own_ne γ
  map_op := own_op γ _ _

instance own_cmra_sep_entails_homomorphism (γ : GName) :
    Algebra.MonoidHomomorphism (CMRA.op (α := A)) sep
      UCMRA.unit iprop(emp) Entails (own (GF := GF) γ) where
  rel_refl := .rfl
  rel_trans := .trans
  op_proper := sep_mono
  map_ne := own_ne γ
  map_op := (own_op γ _ _).1
  map_unit := affine

theorem big_opL_own {B : Type _} (γ : GName) (f : Nat → B → A) (l : List B) (hl : l ≠ []) :
    own (GF := GF) γ ([^ CMRA.op list] k ↦ x ∈ l, f k x) ⊣⊢ [∗list] k ↦ x ∈ l, own γ (f k x) :=
  Algebra.BigOpL.bigOpL_hom_weak f hl

theorem big_opM_own {K : Type _} {M : Type _ → Type _} {B : Type _} [Std.LawfulFiniteMap M K]
    [DecidableEq K] (γ : GName) (g : K → B → A) (m : M B) (hm : ¬ m = (∅ : M B)) :
    own (GF := GF) γ ([^ CMRA.op map] k ↦ x ∈ m, g k x) ⊣⊢ [∗map] k ↦ x ∈ m, own γ (g k x) :=
  Algebra.BigOpM.bigOpM_weak_hom g m (fun he => hm he)

theorem big_opL_own_1 {B : Type _} (γ : GName) (f : Nat → B → A) (l : List B) :
    own (GF := GF) γ ([^ CMRA.op list] k ↦ x ∈ l, f k x) ⊢ [∗list] k ↦ x ∈ l, own γ (f k x) :=
  Algebra.BigOpL.bigOpL_hom f l

theorem big_opM_own_1 {K : Type _} {M : Type _ → Type _} {B : Type _} [Std.LawfulFiniteMap M K]
    (γ : GName) (g : K → B → A) (m : M B) :
    own (GF := GF) γ ([^ CMRA.op map] k ↦ x ∈ m, g k x) ⊢ [∗map] k ↦ x ∈ m, own γ (g k x) :=
  Algebra.BigOpM.bigOpM_hom g m

end big_op_instances

/-! ## Proof mode instances -/
section proofmode_instances
variable {GF : BundledGFunctors} [AllG GF]
variable {A : Type} [CMRA A] {e : Syntax.Cmra} [H : IsCmra (IProp GF) A e]

set_option synthInstance.checkSynthOrder false in
instance into_sep_own {γ} {a b1 b2 : A} [h : IsOp .split a b1 b2] :
    IntoSep (own (GF := GF) γ a) (own γ b1) (own γ b2) where
  into_sep := by rw [h.is_op]; exact (own_op γ _ _).1

set_option synthInstance.checkSynthOrder false in
instance into_and_own {γ} {a b1 b2 : A} [h : IsOp .split a b1 b2] :
    IntoAnd false (own (GF := GF) γ a) (own γ b1) (own γ b2) where
  into_and := by
    rw [h.is_op]
    exact and_intro (own_mono γ _ _ ⟨b2, rfl⟩) (own_mono γ _ _ ⟨b1, CMRA.comm⟩)

set_option synthInstance.checkSynthOrder false in
instance from_sep_own {γ} {a b1 b2 : A} [h : IsOp .split a b1 b2] :
    FromSep (own (GF := GF) γ a) (own γ b1) (own γ b2) where
  from_sep := by rw [h.is_op]; exact (own_op γ _ _).2

set_option synthInstance.checkSynthOrder false in
instance combine_sep_as_own {γ} {a b1 b2 : A} [h : IsOp .merge a b1 b2] :
    CombineSepAs (own (GF := GF) γ b1) (own γ b2) (own γ a) where
  combine_sep_as := by rw [h.is_op]; exact (own_op γ _ _).2

instance combine_sep_gives_own {γ} {a1 a2 : A} :
    CombineSepGives (own (GF := GF) γ a1) (own γ a2) iprop(✓ (a1 • a2)) where
  combine_sep_gives := ((own_op γ a1 a2).2.trans (own_valid γ _))

set_option synthInstance.checkSynthOrder false in
instance from_and_own_persistent {γ} {a b1 b2 : A} [h : IsOp .split a b1 b2]
    [TCOr (CoreId b1) (CoreId b2)] : FromAnd (own (GF := GF) γ a) (own γ b1) (own γ b2) where
  from_and := by
    have _ : TCOr (Persistent (own (GF := GF) γ b1)) (Persistent (own (GF := GF) γ b2)) := by
      cases (inferInstance : TCOr (CoreId b1) (CoreId b2))
      · exact TCOr.l
      · exact TCOr.r
    calc
      _ ⊢ own γ b1 ∗ own γ b2 := persistent_and_sep_mp
      _ ⊢ own γ (b1 • b2) := (own_op γ _ _).2
      _ ⊢ own γ a := by rw [h.is_op]

end proofmode_instances

end Perennial
