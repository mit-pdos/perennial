/-
The loop lemmas and proof-script macros of the proofs of
`partitionOrdered`, `medianOrdered`, `medianAdjacentOrdered`,
`choosePivotOrdered`, `breakPatternsOrdered` and `partitionEqualOrdered`: the `Ordered`
ports of those of the `CmpFunc` functions, reusing their pure lemmas, invariants and
proof scripts.
-/
module

public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Proof.slices.OrderedBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

-- (the proof-script macros come before all proofs: a command such as `macro`
-- declared after asynchronously elaborated proofs waits for them)
set_option hygiene false in
/-- Proof script shared by the two copies in `partitionOrdered`. -/
macro "part_loop1_ord" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · iapply (wp_part_loop1_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

set_option hygiene false in
/-- Proof script shared by the two copies in `partitionOrdered`. -/
macro "part_loop2_ord" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · iapply (wp_part_loop2_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

omit package_sem in
/-- The first inner loop of `partitionOrdered`
(`for i <= j && cmp.Less(data[i], data[a]) { i++ }`), which the Go code contains twice. -/
theorem wp_part_loop1_ord (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr : Loc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ lessImplements (Et := Et) R -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗
      partInv R data a b xp xs i_ptr j_ptr false false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (let: "$a0" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #i_ptr)) in
                let: "$a1" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                  FuncResolve cmp.Less [Et] #() "$a0" "$a1") else
              #false)))
          (Val glv(λ: <>, do: #i_ptr <-[go.int] ![go.int] #i_ptr +⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        partInv R data a b xp xs i_ptr j_ptr true false) }} := by
  iintro #Hpkg #Hless #a #data HI
  unfold lessImplements
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
    wp_apply Hless with %r %Hr
    cases r <;> cleanup_bool_decide
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      refine ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => Or.inr ?_, fun h => h.elim⟩
      intro xi' hxi'
      rw [Hxi_lookup] at hxi'; cases hxi'
      exact fun h => absurd (Hr.2 h) (by simp)
    · wp_auto
      wp_for_post
      iframe
      iexists xs1, (i_val + W64 1), j_val
      iframe
      ipureintro
      refine ⟨by word, ?_, Hpivot, HPerm1, Houtside1, fun h => h.elim, fun h => h.elim⟩
      rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
      exact isPartitionedPre_advance_left R _ _ _ _ _ xp xi Hpart Hpivot Hxi_lookup
        (R_antisym R _ _ (Hr.1 rfl))
  · isplitl []
    · itrivial
    iexists xs1, i_val, j_val
    iframe
    ipureintro
    exact ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => Or.inl (by omega),
      fun h => h.elim⟩

omit package_sem in
/-- The second inner loop of `partitionOrdered`
(`for i <= j && !cmp.Less(data[j], data[a]) { j-- }`), which the Go code contains twice. -/
theorem wp_part_loop2_ord (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr : Loc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ lessImplements (Et := Et) R -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗
      partInv R data a b xp xs i_ptr j_ptr true false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (GoUnOp GoNot go.bool)
                (let: "$a0" :=
                    ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                    let: "$a1" :=
                      ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                      FuncResolve cmp.Less [Et] #() "$a0" "$a1") else
              #false)))
          (Val glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        partInv R data a b xp xs i_ptr j_ptr true true) }} := by
  iintro #Hpkg #Hless #a #data HI
  unfold lessImplements
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
    wp_apply Hless with %r %Hr
    cases r <;> (try simp only [Bool.not_false, Bool.not_true]) <;> cleanup_bool_decide
    · wp_auto
      wp_for_post
      iframe
      iexists xs1, i_val, (j_val - W64 1)
      iframe
      ipureintro
      refine ⟨by word, ?_, Hpivot, HPerm1, Houtside1, fun _ => ?_, fun h => h.elim⟩
      · rw [show sint.nat (j_val - W64 1) = sint.nat j_val - 1 by word]
        exact isPartitionedPre_advance_right R _ _ _ _ _ xp xj Hpart Hpivot Hxj_lookup
          (fun h => absurd (Hr.2 h) (by simp))
      · rcases HBr1 rfl with h | h
        · left; word
        · right; exact h
    · wp_pures
      isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      refine ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => HBr1 rfl, fun _ => Or.inr ?_⟩
      intro xj' hxj'
      rw [Hxj_lookup] at hxj'; cases hxj'
      exact R_antisym R _ _ (Hr.1 rfl)
  · isplitl []
    · itrivial
    iexists xs1, i_val, j_val
    iframe
    ipureintro
    exact ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => HBr1 rfl,
      fun _ => Or.inl (by omega)⟩

omit package_sem in
/-- The first inner loop of `partitionEqualOrdered`
(`for i <= j && !cmp.Less(data[a], data[i]) { i++ }`). -/
theorem wp_peq_loop1_ord (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr : Loc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ lessImplements (Et := Et) R -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗
      peqInv R data a b xp xs i_ptr j_ptr false false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (GoUnOp GoNot go.bool)
                (let: "$a0" :=
                    ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                    let: "$a1" :=
                      ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #i_ptr)) in
                      FuncResolve cmp.Less [Et] #() "$a0" "$a1") else
              #false)))
          (Val glv(λ: <>, do: #i_ptr <-[go.int] ![go.int] #i_ptr +⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        peqInv R data a b xp xs i_ptr j_ptr true false) }} := by
  iintro #Hpkg #Hless #a #data HI
  unfold lessImplements
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
    wp_apply Hless with %r %Hr
    cases r <;> (try simp only [Bool.not_false, Bool.not_true]) <;> cleanup_bool_decide
    · wp_auto
      wp_for_post
      iframe
      iexists xs1, (i_val + W64 1), j_val
      iframe
      ipureintro
      refine ⟨by word, ?_, Hpivot, Hmin, HPerm1, Houtside1, nofun, nofun⟩
      rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
      exact isEqSeg_extend R xs1 _ _ xp xi Hpivot Hsorted Hxi_lookup
        ⟨Hmin xp _ xi ⟨by word, by word⟩ Hpivot Hxi_lookup,
         fun h => absurd (Hr.2 h) (by simp)⟩
    · wp_pures
      isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inr ?_, nofun⟩
      intro xi' hxi'
      rw [Hxi_lookup] at hxi'; cases hxi'
      exact R_antisym R _ _ (Hr.1 rfl)
  · isplitl []
    · itrivial
    iexists xs1, i_val, j_val
    iframe
    ipureintro
    exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inl (by omega),
      nofun⟩

omit package_sem [StrictWeakOrder R] in
/-- The second inner loop of `partitionEqualOrdered`
(`for i <= j && cmp.Less(data[a], data[j]) { j-- }`). -/
theorem wp_peq_loop2_ord (data : GoSlice) (a b : w64) (xp : E) (xs : List E)
    (i_ptr j_ptr data_ptr a_ptr : Loc)
    (Hab_bound : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62)
    (Hlen : xs.length = sint.nat data.len ∧ 0 ≤ sint.Z data.len) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.slices -∗ lessImplements (Et := Et) R -∗
      a_ptr ↦□ a -∗ data_ptr ↦□ data -∗
      peqInv R data a b xp xs i_ptr j_ptr true false -∗
      WP (App (App (App (Val doFor)
          (Val glv(λ: <>,
            if: ![go.int] #i_ptr ≤⟨go.int⟩ ![go.int] #j_ptr then
              (let: "$a0" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #a_ptr)) in
                let: "$a1" :=
                  ![Et] ((IndexRef Et.SliceType) (![Et.SliceType] #data_ptr, ![go.int] #j_ptr)) in
                  FuncResolve cmp.Less [Et] #() "$a0" "$a1") else
              #false)))
          (Val glv(λ: <>, do: #j_ptr <-[go.int] ![go.int] #j_ptr -⟨go.int⟩ #(W64 1))))
          (Val glv(λ: <>, #())))
      {{ fun v => iprop(⌜v = executeVal⌝ ∗
        peqInv R data a b xp xs i_ptr j_ptr true true) }} := by
  iintro #Hpkg #Hless #a #data HI
  unfold lessImplements
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
    wp_apply Hless with %r %Hr
    cases r <;> cleanup_bool_decide
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
        fun _ => Or.inr ?_⟩
      intro xj' hxj'
      rw [Hxj_lookup] at hxj'; cases hxj'
      exact fun h => absurd (Hr.2 h) (by simp)
    · wp_auto
      wp_for_post
      iframe
      iexists xs1, i_val, (j_val - W64 1)
      iframe
      ipureintro
      refine ⟨by word, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => ?_, nofun⟩
      rcases HBr1 rfl with h | h
      · left; word
      · right; exact h
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
