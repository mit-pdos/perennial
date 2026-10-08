/-
Specs of
`partitionOrdered`, `medianOrdered`, `medianAdjacentOrdered`,
`choosePivotOrdered`, `breakPatternsOrdered` and `partitionEqualOrdered`: the `Ordered`
ports of `pdqSort/partition.lean`, reusing its pure lemmas, invariants and proof scripts.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.slices
import Perennial.GeneratedProof.slices
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.slices_proof.pdqSort.sort_basics
import Perennial.Proof.slices_proof.pdqSort.partition
import Perennial.Proof.slices_proof.pdqSortOrdered.ordered_basics

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

theorem wp_partitionOrdered (data : GoSlice) (a b pivot : w64)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (Val #(functions partitionOrdered [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #pivot))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
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
  ihave HI : partInv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i xi xa' _ _; constructor <;> intro <;> word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
  part_loop1_ord
  part_loop2_ord
  part_load_j
  wp_if_destruct
  · part_finish
  · part_swap
    clear Hpart Hpivot HPerm1 Houtside1 HBr1 HBr2 HBr1' HBr2' Hlen2 Hxi_lookup Hxj_lookup ij_bound Hif Hle
      xs1 i_val j_val xi xj
    wp_for
    part_loop1_ord
    part_loop2_ord
    part_load_j
    wp_if_destruct
    · wp_for_post
      part_finish
    · part_swap
      wp_for_post
      unfold partInv
      simp only [Bool.false_eq_true]
      iframe

theorem wp_medianOrdered (data : GoSlice) (a b c : w64) (swaps_l : Loc)
    (dq : DFrac) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(0 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int)) ∧
                      (0 ≤ sint.Z b ∧ sint.Z b < (xs.length : Int)) ∧
                      (0 ≤ sint.Z c ∧ sint.Z c < (xs.length : Int))⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (App (App (App (App (Val #(functions medianOrdered [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #c)) (Val #swaps_l))
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
  wp_apply wp_order2Ordered R data a b swaps_l dq xs swaps xa xb (by omega) (by omega)
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2Ordered R data b c swaps_l dq xs sw1 xb xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2Ordered R data a b swaps_l dq xs sw2 xa xb (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2Ordered R data a c swaps_l dq xs sw2 xa xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2Ordered R data a c swaps_l dq xs sw1 xa xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2Ordered R data b a swaps_l dq xs sw2 xb xa (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2Ordered R data b c swaps_l dq xs sw2 xb xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

theorem wp_medianAdjacentOrdered (data : GoSlice) (a : w64) (swaps_l : Loc)
    (dq : DFrac) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (App (App (Val #(functions medianAdjacentOrdered [Et])) (Val #data)) (Val #a))
        (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        data ↦*{dq} xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_medianOrdered R data (a - W64 1) a (a + W64 1) swaps_l dq xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

theorem wp_choosePivotOrdered (data : GoSlice) (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val #(functions choosePivotOrdered [Et])) (Val #data)) (Val #a))
        (Val #b))
    {{ (r : w64) (hint : slices.sortedHint), RET (PairV #r #hint);
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
  obtain ⟨Hi, Hj, Hk⟩ := part_choosePivot_idx a b d xs.length Hab_bound Hd
  wp_if_destruct
  · have h8 : 8 ≤ sint.Z b - sint.Z a := by rw [← Hl]; exact Hif
    wp_if_destruct
    · wp_apply wp_medianAdjacentOrdered R data (a + d * 1) swaps_ptr (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %ri %sw1 ⟨Hxs, %Hri, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi]; omega
      wp_apply wp_medianAdjacentOrdered R data (a + d * 2) swaps_ptr (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rj %sw2 ⟨Hxs, %Hrj, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hj]; omega
      wp_apply wp_medianAdjacentOrdered R data (a + d * 3) swaps_ptr (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rk %sw3 ⟨Hxs, %Hrk, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hk]; omega
      rw [Hi] at Hri; rw [Hj] at Hrj; rw [Hk] at Hrk
      wp_apply wp_medianOrdered R data ri rj rk swaps_ptr (DFrac.own 1) xs _
        $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
    · wp_apply wp_medianOrdered R data (a + d * 1) (a + d * 2) (a + d * 3) swaps_ptr
        (DFrac.own 1) xs _ $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi, Hj, Hk]; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
  · have : sint.Z a ≤ sint.Z (a + d * 2) ∧ sint.Z (a + d * 2) < sint.Z b := by
      rw [Hj]; omega
    (try wp_if_destruct) <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)


theorem wp_breakPatternsOrdered (data : GoSlice) (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (Val #(functions breakPatternsOrdered [Et])) (Val #data)) (Val #a))
        (Val #b))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_if_destruct
  · wp_apply wp_nextPowerOfTwo with %m %Hm
    have hL : sint.Z (b - a) = sint.Z b - sint.Z a := by word
    have hd : sint.Z (BitVec.sdiv (b - a) (W64 4)) = (sint.Z b - sint.Z a) / 4 := by
      rw [sint_sdiv4 _ (by omega), hL]
    ihave HI : (∃ (xs1 : List E) (idx_val : w64) (rv : xorshift),
        "Hxs" ∷ data ↦* xs1 ∗
        "idx" ∷ idx_ptr ↦ idx_val ∗
        "random" ∷ random_ptr ↦ rv ∗
        "%idx_bound" ∷ ⌜sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 - 1 ≤ sint.Z idx_val ∧
          sint.Z idx_val ≤ sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 + 2⌝ ∗
        "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
        "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [Hxs idx random]
    · iexists xs, _, _
      iframe
      ipureintro
      exact ⟨by word, List.Perm.refl _, outsideSame_refl _ _ _⟩
    wp_for HI
    wp_if_destruct
    · wp_apply xorshift.wp_Next $$ random with %n ⟨%rv', random⟩
      have hand : uint.Z (n &&& (m - W64 1)) ≤ uint.Z (m - W64 1) := by
        have := Nat.and_le_right (n := n.toNat) (m := (m - W64 1).toNat)
        simp only [uint.Z, BitVec.toNat_and]; omega
      have hm1 : uint.Z (m - W64 1) = uint.Z m - 1 := by word
      have ho : sint.Z (n &&& (m - W64 1)) = uint.Z (n &&& (m - W64 1)) := by
        have h63 : uint.Z (n &&& (m - W64 1)) < 2 ^ 63 := by omega
        exact BitVec.toInt_eq_toNat_of_lt (by unfold uint.Z at h63; omega)
      have Hl := HPerm1.length_eq
      -- `if other >= length { other -= length }`, joined
      wp_join iprop(∃ o : w64, "other" ∷ other_ptr ↦ o ∗ "length" ∷ length_ptr ↦ (b - a) ∗
          "%Ho" ∷ ⌜0 ≤ sint.Z o ∧ sint.Z o < sint.Z b - sint.Z a⌝) with [other length]
          as ⟨%o, other, length, %Ho⟩
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      have hj : sint.Z a ≤ sint.Z (a + o) ∧ sint.Z (a + o) < sint.Z b := by
        constructor <;> word
      generalize hjdef : (a + o) = j at *
      ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
      have hi : sint.Z a ≤ sint.Z idx_val ∧ sint.Z idx_val < sint.Z b := by
        have := hd; constructor <;> word
      list_elem xs1 (sint.nat j) as xo
      list_elem xs1 (sint.nat idx_val) as xi
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z j) xs1 _ xo (by word) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxo_lookup
      slice_index_if
      wp_apply wp_load_slice_index data (sint.Z idx_val) xs1 _ xi (by word) $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact Hxi_lookup
      slice_index_if
      wp_pures
      wp_apply wp_store_slice_index data (sint.Z idx_val) xs1 xo $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; constructor <;> word
      slice_index_if
      wp_pures
      rw [hjdef]
      wp_apply wp_store_slice_index data (sint.Z j) _ xi $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; simp only [List.length_set]; constructor <;> word
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by have := hd; word, ?_, ?_⟩
      · exact HPerm1.trans (swap_perm xs1 (sint.nat j) (sint.nat idx_val) xo xi
          Hxo_lookup Hxi_lookup)
      · exact outsideSame_trans _ _ _ _ _ Houtside1
          (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
    · iapply HΦ
      iframe
      ipureintro
      exact ⟨HPerm1, Houtside1⟩
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, outsideSame_refl _ _ _⟩


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


theorem wp_partitionEqualOrdered (data : GoSlice) (a b pivot : w64)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ ∗
        "%Hmin" ∷ ⌜OneLeSeg R xs (sint.nat pivot) (sint.nat a) (sint.nat b)⌝ }}
      (App (App (App (App (Val #(functions partitionEqualOrdered [Et])) (Val #data))
        (Val #a)) (Val #b)) (Val #pivot))
    {{ (xs' : List E) (r : w64), RET #r;
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a < sint.Z r ∧ sint.Z r ≤ sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsEqPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
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
  ihave HI : peqInv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold peqInv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i j xi xj hb; word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact peq_init_min R xs _ _ _ xp xa Hxp_lookup Hxa_lookup ⟨by word, by word⟩ Hmin
  wp_for
  -- first inner loop: `for i <= j && !less(data[a], data[i]) { i++ }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · iapply (wp_peq_loop1_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  -- second inner loop: `for i <= j && less(data[a], data[j]) { j-- }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · iapply (wp_peq_loop2_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  unfold peqInv
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
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ (by word) (by word))


end proof

end slices

end Perennial
end
