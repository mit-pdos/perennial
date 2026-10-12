/-
Shared definitions of the proofs of `order2`, `median`, `medianAdjacent`, `choosePivot`,
`breakPatterns`, `partition` and `partitionEqual` over a `sort.Interface` (the `CmpFunc`
proofs of `slices`, `Perennial/Proof/slices/partitionCmpFunc.lean` and its neighbors, with
`Less`/`Swap` calls): the proof-script macros of `partition`, `Swap` in the raw form
`isSorter` states it, and the loop invariants of `partition` and `partitionEqual`.
-/
module

public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

open slices

-- (the proof-script macros come before all proofs, as in `slices`)
/-- `bool_if`, also for a negated literal (`!true`, `!false`). -/
macro "bool_if'" : tactic =>
  `(tactic| (simp only [Bool.not_false, Bool.not_true, decide_eq_true_eq, false_neq_true,
    true_neq_false, ↓reduceIte]))

set_option hygiene false in
/-- The first inner loop of `partition` (`for i <= j && data.Less(i, a) { i++ }`), which the
Go code contains twice. -/
macro "part_loop1" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv own R a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · unfold partInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat i_val) as xi
      wp_apply wp_sorter_Less x own R xs1 i_val a xi xp (by word) (by word) Hxi_lookup Hpivot
        $$ [Hxs] as %r ⟨Hxs, %Hr⟩
      · iframe; iexact Hsrt
      cases r
      · bool_if'
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hpart, Hpivot, HPerm1, Houtside1, fun _ => Or.inr ?_, fun h => h.elim⟩
        intro xi' hxi'
        rw [Hxi_lookup] at hxi'; cases hxi'
        exact fun h => by simpa using Hr.2 h
      · bool_if'
        wp_auto
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
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)))

set_option hygiene false in
/-- The second inner loop of `partition` (`for i <= j && !data.Less(j, a) { j-- }`). -/
macro "part_loop2" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    partInv own R a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · unfold partInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat j_val) as xj
      wp_apply wp_sorter_Less x own R xs1 j_val a xj xp (by word) (by word) Hxj_lookup Hpivot
        $$ [Hxs] as %r ⟨Hxs, %Hr⟩
      · iframe; iexact Hsrt
      cases r
      · bool_if'
        wp_auto
        wp_for_post
        iframe
        iexists xs1, i_val, (j_val - W64 1)
        iframe
        ipureintro
        refine ⟨by word, ?_, Hpivot, HPerm1, Houtside1, fun _ => ?_, fun h => h.elim⟩
        · rw [show sint.nat (j_val - W64 1) = sint.nat j_val - 1 by word]
          exact isPartitionedPre_advance_right R _ _ _ _ _ xp xj Hpart Hpivot Hxj_lookup
            (fun h => by simpa using Hr.2 h)
        · rcases HBr1 rfl with h | h
          · left; word
          · right; exact h
      · bool_if'
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
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)))

set_option hygiene false in
/-- After the two inner loops of `partition`: destruct the invariant. -/
macro "part_load_j" : tactic => `(tactic| (
  unfold partInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  list_elem xs1 (sint.nat j_val) as xj
  (try wp_auto)))

set_option hygiene false in
/-- `data.Swap(j, a); return j, ...` of `partition`. -/
macro "part_finish" : tactic => `(tactic| (
  wp_apply wp_sorter_Swap_raw x own R xs1 j_val a xj xp (by word) (by word) Hxj_lookup Hpivot
    $$ [Hxs] as Hxs
  · iframe; iexact Hsrt
  (try wp_auto)
  iapply HΦ
  iframe Hxs
  ipureintro
  exact part_finish_pure R xs xs1 a b i_val j_val xp xj Hab_bound ij_bound Hpart Hpivot HPerm1
    Houtside1 Hlen2 Hxj_lookup (by word)))

set_option hygiene false in
/-- `data.Swap(i, j); i++; j--` of `partition`, re-establishing the invariant. -/
macro "part_swap" : tactic => `(tactic| (
  have Hle : sint.Z i_val ≤ sint.Z j_val := by word
  obtain ⟨xi, Hxi_lookup⟩ := lookup_lt_is_Some_2 (l := xs1) (i := sint.nat i_val) (by word)
  have HBr1' := HBr1 rfl
  have HBr2' := HBr2 rfl
  wp_apply wp_sorter_Swap_raw x own R xs1 i_val j_val xi xj (by word) (by word) Hxi_lookup
    Hxj_lookup $$ [Hxs] as Hxs
  · iframe; iexact Hsrt
  (try wp_auto)
  ihave HI : partInv own R a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    exact part_swap_pure R xs xs1 a b i_val j_val xp xi xj Hab_bound ij_bound Hpart Hpivot HPerm1
      Houtside1 Hlen2 Hxj_lookup Hle Hxi_lookup HBr1' HBr2'))

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]
variable {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF)
variable (R : E → E → Prop) [StrictWeakOrder R]

omit [StrictWeakOrder R] in
/-- `Swap(i, j)` with the result as `isSorter` states it, `(l.set i l[j]).set j l[i]`: the
form of the slice proofs' `data[i], data[j] = data[j], data[i]` (two stores, `i` first). -/
theorem wp_sorter_Swap_raw (l : List E) (i j : w64) (a b : E) (hi : 0 ≤ sint.Z i)
    (hj : 0 ≤ sint.Z j) (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ isSorter x own R ∗ own l }}
      (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
    {{ RET #(); own ((l.set (sint.nat i) b).set (sint.nat j) a) }} := by
  iintro %Φ ⟨#Hs, Hl⟩ HΦ
  unfold isSorter
  icases Hs with ⟨-, -, #HSwap⟩
  iapply HSwap $$ %l %i %j %a %b [] Hl HΦ
  ipureintro; exact ⟨hi, hj, ha, hb⟩

omit [StrictWeakOrder R] in
/-- The loop invariant of `partition`, as `slices.partInv` with `own` (`br1`/`br2` record
that the first/second inner loop has exited). -/
def partInv (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : Loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ own xs1 ∗
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

omit [StrictWeakOrder R] in
/-- The loop invariant of `partitionEqual`, as `slices.peqInv` with `own`. -/
def peqInv (a b : w64) (xp : E) (xs : List E) (i_ptr j_ptr : Loc)
    (br1 br2 : Bool) : IProp GF :=
  iprop(∃ (xs1 : List E) (i_val j_val : w64),
    "Hxs" ∷ own xs1 ∗
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

end defs

end sort

end Perennial
end
