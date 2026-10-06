/-
Port of `new/proof/slices_proof/pdqSort/sort_basics.v`: order relations,
list facts and the spec of `order2CmpFunc` shared by the `pdqsort` proofs.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.slices
import Perennial.GeneratedProof.slices
import Perennial.Proof.slices_proof.slices_init

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
/-- Discharge the bounds check of a slice index: rewrite the first
`if c then _ else _` in the goal to its `then` branch, proving `c` (a conjunction
of word inequalities) with `word`. -/
macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

class WeakOrder {A : Type} (R : A → A → Prop) : Prop where
  weak_order_irrefl : ∀ x, ¬ R x x
  weak_order_anti_symm : ∀ x y, R x y ↔ ¬ R y x
  weak_order_trans : ∀ x y z, R x y → R y z → R x z

theorem WeakOrder_Improper (R : Int → Int → Prop) : WeakOrder R → False := by
  intro H
  have h0 := H.weak_order_irrefl 0
  exact h0 ((H.weak_order_anti_symm 0 0).2 h0)

class StrictWeakOrder {A : Type} (R : A → A → Prop) : Prop where
  strict_weak_order_irrefl : ∀ x, ¬ R x x
  strict_weak_order_trans : ∀ x y z, R x y → R y z → R x z
  strict_weak_order_equiv : Equivalence (fun x y => ¬ R x y ∧ ¬ R y x)

theorem StrictWeakOrder_unsigned_lt :
    StrictWeakOrder (fun (a b : w64) => uint.Z a < uint.Z b) where
  strict_weak_order_irrefl _ := by omega
  strict_weak_order_trans _ _ _ h1 h2 := by omega
  strict_weak_order_equiv :=
    ⟨fun _ => by omega, fun h => by omega, fun h1 h2 => by omega⟩

theorem StrictWeakOrder_signed_lt :
    StrictWeakOrder (fun (a b : w64) => sint.Z a < sint.Z b) where
  strict_weak_order_irrefl _ := by omega
  strict_weak_order_trans _ _ _ h1 h2 := by omega
  strict_weak_order_equiv :=
    ⟨fun _ => by omega, fun h => by omega, fun h1 h2 => by omega⟩

theorem swap_perm {T : Type} (xs : List T) (i j : Nat) (xi xj : T)
    (hi : xs[i]? = some xi) (hj : xs[j]? = some xj) :
    xs ≡ₚ (<[i := xj]> (<[j := xi]> xs)) :=
  (Permutation_insert_swap xs j i xj xi hj hi).symm

def OutsideSame {T : Type} (xs xs' : List T) (a b : Nat) : Prop :=
  ∀ i, i < a ∨ i ≥ b → xs[i]? = xs'[i]?

theorem outsideSame_refl {T : Type} (xs : List T) (a b : Nat) : OutsideSame xs xs a b :=
  fun _ _ => rfl

theorem outsideSame_trans {T : Type} (a b : Nat) (xs0 xs1 xs2 : List T) :
    OutsideSame xs0 xs1 a b → OutsideSame xs1 xs2 a b → OutsideSame xs0 xs2 a b :=
  fun h1 h2 i hi => (h1 i hi).trans (h2 i hi)

theorem outsideSame_swap {T : Type} (xs : List T) (i j : Nat) (xi xj : T) (a b : Nat)
    (hi : a ≤ i ∧ i < b) (hj : a ≤ j ∧ j < b) :
    OutsideSame xs (<[i := xj]> (<[j := xi]> xs)) a b := by
  intro k hk
  rw [list_lookup_insert_ne _ _ (by omega), list_lookup_insert_ne _ _ (by omega)]

theorem outsideSame_loosen {T : Type} (xs xs' : List T) (a b a1 b1 : Nat) :
    OutsideSame xs xs' a b → a1 ≤ a → b1 ≥ b → OutsideSame xs xs' a1 b1 :=
  fun h ha hb i hi => h i (by omega)

theorem outsideSame_decompose {T : Type} (xsa xsb : List T) (a b : Nat)
    (H : OutsideSame xsa xsb a b) (hab : a ≤ b) :
    xsa = xsa.take a ++ (xsa.drop a).take (b - a) ++ xsa.drop b ∧
    xsb = xsa.take a ++ (xsb.drop a).take (b - a) ++ xsa.drop b := by
  have split : ∀ (l : List T), l = l.take a ++ (l.drop a).take (b - a) ++ l.drop b := by
    intro l
    rw [List.append_assoc]
    conv => lhs; rw [← List.take_append_drop a l]
    congr 1
    rw [show b = a + (b - a) by omega, ← List.drop_drop]
    conv => rhs; rw [show a + (b - a) - a = b - a by omega]
    exact (List.take_append_drop _ _).symm
  have hd : xsa.drop b = xsb.drop b := by
    apply List.ext_getElem?; intro i
    rw [List.getElem?_drop, List.getElem?_drop]; exact H _ (by omega)
  have ht : xsa.take a = xsb.take a := by
    apply List.ext_getElem?; intro i
    by_cases hi : i < a
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]; exact H _ (by omega)
    · rw [List.getElem?_take_eq_none (by omega), List.getElem?_take_eq_none (by omega)]
  refine ⟨split xsa, ?_⟩
  rw [ht, hd]; exact split xsb

theorem Permutation_existsIndex {T : Type} (xs xs' : List T) (i a b : Nat) (x : T)
    (Hperm : xs ≡ₚ xs') (Hsame : OutsideSame xs xs' a b)
    (Hb : (a ≤ i ∧ i < b) ∧ b ≤ xs.length) (Hx : xs[i]? = some x) :
    ∃ i0, xs'[i0]? = some x ∧ (a ≤ i0 ∧ i0 < b) := by
  obtain ⟨Hxs, Hxs'⟩ := outsideSame_decompose xs xs' a b Hsame (by omega)
  have Hmid : (xs.drop a).take (b - a) ≡ₚ (xs'.drop a).take (b - a) := by
    have h := Hperm
    rw [Hxs, Hxs'] at h
    rw [List.append_assoc, List.append_assoc] at h
    exact (List.perm_append_right_iff _).1 ((List.perm_append_left_iff _).1 h)
  have hx : x ∈ (xs.drop a).take (b - a) := by
    apply List.mem_of_getElem? (i := i - a)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      show a + (i - a) = i by omega, Hx]
  obtain ⟨j0, hj0, hget⟩ := List.getElem_of_mem (Hmid.mem_iff.1 hx)
  have hlen : ((xs'.drop a).take (b - a)).length ≤ b - a := by simp; omega
  refine ⟨a + j0, ?_, by omega, by omega⟩
  have := List.getElem?_eq_getElem hj0
  rw [hget, List.getElem?_take_of_lt (by omega), List.getElem?_drop] at this
  exact this

section order
variable {E : Type} (R : E → E → Prop) [SWO : StrictWeakOrder R]

theorem R_antisym : ∀ x y, R x y → ¬ R y x := by
  intro x y h1 h2
  exact SWO.strict_weak_order_irrefl x (SWO.strict_weak_order_trans _ _ _ h1 h2)

theorem notR_refl : ∀ x, ¬ R x x := SWO.strict_weak_order_irrefl

theorem notR_trans : ∀ x y z, ¬ R z y → ¬ R y x → ¬ R z x := by
  intro x y z Hzy Hyx Hzx
  have trans1 := SWO.strict_weak_order_trans
  by_cases h1 : R x y
  · exact R_antisym R x z (trans1 _ _ _ h1 (Classical.byContradiction fun h => by
      exact absurd (trans1 _ _ _ Hzx h1) Hzy)) Hzx
  by_cases h2 : R y z
  · exact Hyx (trans1 _ _ _ h2 Hzx)
  · have := SWO.strict_weak_order_equiv.trans (x := z) (y := y) (z := x) ⟨Hzy, h2⟩ ⟨Hyx, h1⟩
    exact this.1 Hzx

theorem notR_comparable : ∀ x y, ¬ R x y ∨ ¬ R y x := by
  intro x y
  by_cases h : R x y
  · exact Or.inr (R_antisym R x y h)
  · exact Or.inl h

theorem comparison_negate (r : w64) (x y : E) :
    (sint.Z r < 0 ↔ R x y) → (¬ (sint.Z r < 0) ↔ ¬ R x y) := by
  intro H; exact not_congr H

end order

section sorted
variable {E : Type} (R : E → E → Prop)

def is_sorted (l : List E) : Prop :=
  ∀ (i j : Nat) xi xj, i < j → l[i]? = some xi → l[j]? = some xj → ¬ R xj xi

def IsSortedSeg (l : List E) (st ed : Nat) : Prop :=
  ∀ (i j : Nat) xi xj, (st ≤ i ∧ i < j) ∧ j < ed →
    l[i]? = some xi → l[j]? = some xj → ¬ R xj xi

theorem isSortedSeg_is_sorted (l : List E) :
    IsSortedSeg R l 0 l.length → is_sorted R l := by
  intro H i j xi xj hij hi hj
  exact H i j xi xj ⟨⟨by omega, hij⟩, lookup_lt_Some hj⟩ hi hj

def OneLeSeg (xs : List E) (i l r : Nat) : Prop :=
  ∀ xi (j : Nat) xj, l ≤ j ∧ j < r → xs[i]? = some xi → xs[j]? = some xj → ¬ R xj xi

def header (xs : List E) (a b : Nat) : Prop :=
  if a = 0 then True else OneLeSeg R xs (a - 1) a b

theorem header_preserve (xs xs' : List E) (a b : Nat) :
    header R xs a b → xs ≡ₚ xs' → OutsideSame xs xs' a b → b ≤ xs.length →
    header R xs' a b := by
  unfold header OneLeSeg OutsideSame
  intro H Hperm Hsame Hb
  by_cases ha : a = 0
  · simp [ha]
  simp only [ha, ↓reduceIte] at H ⊢
  intro xi j xj Hj Hxi Hxj
  rw [← Hsame _ (by omega)] at Hxi
  obtain ⟨i0, Hi0, Hi0b⟩ := Permutation_existsIndex xs' xs j a b xj Hperm.symm
    (fun i hi => (Hsame i hi).symm) ⟨Hj, by rw [← Hperm.length_eq]; omega⟩ Hxj
  exact H xi i0 xj Hi0b Hxi Hi0

end sorted

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop)

/-- The comparison function implements `R`. The sort implementation only ever
checks `cmp x y < 0`; it does not distinguish between 0 and positive
comparisons. -/
def cmpImplements (cmp_code : func.t) : IProp GF :=
  iprop(∀ (x y : E),
    {{ True }}
      (App (App (Val #cmp_code) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }})

instance cmpImplements_persistent (cmp_code : func.t) :
    Persistent (cmpImplements (GF := GF) R cmp_code) := by
  unfold cmpImplements; infer_instance

theorem wp_order2CmpFunc [StrictWeakOrder R] (data : slice.t) (a b : w64) (swaps_l : Loc)
    (cmp_code : func.t) (dq : DFrac) (xs : List E) (swaps : w64) (xa xb : E)
    (Ha_bound : 0 ≤ sint.Z a) (Hb_bound : 0 ≤ sint.Z b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hcmp" ∷ cmpImplements R cmp_code }}
      (App (App (App (App (App (Val #(functions order2CmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #swaps_l)) (Val #cmp_code))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        data ↦*{dq} xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have := lookup_lt_Some Hxa
  have := lookup_lt_Some Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z b) xs dq xb Hb_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs dq xa Ha_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa
  unfold cmpImplements
  wp_apply Hcmp with %r %Hr
  wp_if_destruct
  · iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 (by word)⟩
  · iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => Hif (by have := Hr.2 h; word)⟩

end proof

end slices

end Perennial
end
