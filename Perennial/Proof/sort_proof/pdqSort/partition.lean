/-
Specs of `order2`, `median`, `medianAdjacent`, `choosePivot`, `breakPatterns`,
`partition` and `partitionEqual` over a `sort.Interface`, and of `xorshift.Next` and
`nextPowerOfTwo` (`slices_proof/pdqSort/partition.lean` with `Less`/`Swap` calls).
-/
module

public import Perennial.Proof.sort_proof.pdqSort.sort_basics
public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Proof.math.bits

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

section proof
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

theorem wp_order2 (a b : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) (xa xb : E)
    (Ha_bound : 0 ≤ sint.Z a) (Hb_bound : 0 ≤ sint.Z b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (Val (@! order2)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #swaps_l))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        own xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_sorter_Less x own R xs b a xb xa Hb_bound Ha_bound Hxb Hxa $$ [$Hsrt $Hxs]
    as %r ⟨Hxs, %Hr⟩
  cases r
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => by simpa using Hr.2 h⟩
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 rfl⟩

theorem wp_median (a b c : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hbounds" ∷ ⌜(0 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int)) ∧
                      (0 ≤ sint.Z b ∧ sint.Z b < (xs.length : Int)) ∧
                      (0 ≤ sint.Z c ∧ sint.Z c < (xs.length : Int))⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (App (Val (@! median)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #c)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        own xs ∗
        ⌜r = a ∨ r = b ∨ r = c⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat a) as xa
  list_elem xs (sint.nat b) as xb
  list_elem xs (sint.nat c) as xc
  wp_apply wp_order2 x own R a b swaps_l xs swaps xa xb (by omega) (by omega)
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2 x own R b c swaps_l xs sw1 xb xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2 x own R a b swaps_l xs sw2 xa xb (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 x own R a c swaps_l xs sw2 xa xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2 x own R a c swaps_l xs sw1 xa xc (by omega) (by omega)
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2 x own R b a swaps_l xs sw2 xb xa (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 x own R b c swaps_l xs sw2 xb xc (by omega) (by omega)
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

theorem wp_medianAdjacent (a : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (Val (@! medianAdjacent)) (Val #(interface.ok x))) (Val #a)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        own xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_median x own R (a - W64 1) a (a + W64 1) swaps_l xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

theorem wp_choosePivot (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val (@! choosePivot)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (r : w64) (hint : sort.sortedHint), RET (PairV #r #hint);
        own xs ∗
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
    · wp_apply wp_medianAdjacent x own R (a + d * 1) swaps_ptr
        xs _ $$ [Hxs swaps] with %ri %sw1 ⟨Hxs, %Hri, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi]; omega
      wp_apply wp_medianAdjacent x own R (a + d * 2) swaps_ptr
        xs _ $$ [Hxs swaps] with %rj %sw2 ⟨Hxs, %Hrj, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hj]; omega
      wp_apply wp_medianAdjacent x own R (a + d * 3) swaps_ptr
        xs _ $$ [Hxs swaps] with %rk %sw3 ⟨Hxs, %Hrk, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hk]; omega
      rw [Hi] at Hri; rw [Hj] at Hrj; rw [Hk] at Hrk
      wp_apply wp_median x own R ri rj rk swaps_ptr xs _
        $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
    · wp_apply wp_median x own R (a + d * 1) (a + d * 2) (a + d * 3) swaps_ptr
        xs _ $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi, Hj, Hk]; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
  · have : sint.Z a ≤ sint.Z (a + d * 2) ∧ sint.Z (a + d * 2) < sint.Z b := by
      rw [Hj]; omega
    (try wp_if_destruct) <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)

omit [StrictWeakOrder R] in
theorem xorshift.wp_Next (r : Loc) (v : xorshift) :
    {{ (r ↦ v : IProp GF) }}
      (App (Val (r @!! go.GoType.PointerType xorshift.ty @!! go!"Next")) (Val #()))
    {{ (v' : xorshift) (n : w64), RET #n; r ↦ v' }} := by
  wp_start as Hr
  wp_auto
  wp_end

omit [StrictWeakOrder R] in
theorem wp_nextPowerOfTwo (length : w64) (h : 0 < sint.Z length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort }}
      (App (Val (@! nextPowerOfTwo)) (Val #length))
    {{ (m : w64), RET #m; ⌜sint.Z length < uint.Z m ∧ uint.Z m ≤ 2 * sint.Z length⌝ }} := by
  wp_start
  wp_auto
  wp_apply math.bits.wp_Len_exact with %l %Hl
  iapply HΦ
  ipureintro
  obtain ⟨_, Hlt, Hle⟩ := Hl
  have hu : uint.Z length = sint.Z length := by word
  rcases Hle with Hle | Hle
  · subst Hle; simp at h
  have hl63 : uint.nat l < 64 := by
    rcases Nat.lt_or_ge (uint.nat l) 64 with h' | h'
    · exact h'
    · exfalso
      have : (2 : Int) ^ 64 ≤ 2 ^ uint.nat l := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) h'
        exact_mod_cast this
      have : uint.Z length < 2 ^ 63 := by word
      omega
  have hshift : uint.Z (W64 1 <<< l) = 2 ^ uint.nat l := by
    rw [show uint.Z (W64 1 <<< l) = ((W64 1 <<< l).toNat : Int) from rfl, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
    simp only [show (W64 1).toNat = 1 from rfl, Nat.one_shiftLeft]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by decide) hl63)]
    norm_cast
  rw [hshift]
  omega

theorem wp_breakPatterns (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a < sint.Z b⌝ }}
      (App (App (App (Val (@! breakPatterns)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (xs' : List E), RET #();
        own xs' ∗
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
        "Hxs" ∷ own xs1 ∗
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
    · wp_apply xorshift.wp_Next $$ random with %rv' %n random
      have hand : uint.Z (n &&& (m - W64 1)) ≤ uint.Z (m - W64 1) := by
        have := Nat.and_le_right (n := n.toNat) (m := (m - W64 1).toNat)
        simp only [uint.Z, BitVec.toNat_and]; omega
      have hm1 : uint.Z (m - W64 1) = uint.Z m - 1 := by word
      have ho : sint.Z (n &&& (m - W64 1)) = uint.Z (n &&& (m - W64 1)) := by
        have h63 : uint.Z (n &&& (m - W64 1)) < 2 ^ 63 := by omega
        exact BitVec.toInt_eq_toNat_of_lt (by unfold uint.Z at h63; omega)
      have Hl := HPerm1.length_eq
      wp_join iprop(∃ o : w64, "other" ∷ other_ptr ↦ o ∗ "length" ∷ length_ptr ↦ (b - a) ∗
          "%Ho" ∷ ⌜0 ≤ sint.Z o ∧ sint.Z o < sint.Z b - sint.Z a⌝) with [other length]
          as ⟨%o, other, length, %Ho⟩
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      have hj : sint.Z a ≤ sint.Z (a + o) ∧ sint.Z (a + o) < sint.Z b := by
        constructor <;> word
      generalize hjdef : (a + o) = j at *
      have hi : sint.Z a ≤ sint.Z idx_val ∧ sint.Z idx_val < sint.Z b := by
        have := hd; constructor <;> word
      list_elem xs1 (sint.nat j) as xo
      list_elem xs1 (sint.nat idx_val) as xi
      wp_apply wp_sorter_Swap_raw x own R xs1 idx_val j xi xo (by word) (by word)
        Hxi_lookup Hxo_lookup $$ [$Hsrt $Hxs] as Hxs
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

theorem wp_partition (a b pivot : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (Val (@! partition)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #pivot))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        own xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  wp_apply wp_sorter_Swap_raw x own R xs a pivot xa xp (by omega) (by omega)
    Hxa_lookup Hxp_lookup $$ [$Hsrt $Hxs] as Hxs
  (try wp_auto)
  ipersist a
  ipersist data
  ihave HI : partInv own R a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · intro i xi xa' _ _; constructor <;> intro <;> word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup
    · exact outsideSame_swap _ _ _ _ _ _ _ (by word) (by word)
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
      unfold partInv
      simp only [Bool.false_eq_true]
      iframe

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

theorem wp_partitionEqual (a b pivot : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ ∗
        "%Hmin" ∷ ⌜OneLeSeg R xs (sint.nat pivot) (sint.nat a) (sint.nat b)⌝ }}
      (App (App (App (App (Val (@! partitionEqual)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #pivot))
    {{ (xs' : List E) (r : w64), RET #r;
        own xs' ∗
        "%range" ∷ ⌜sint.Z a < sint.Z r ∧ sint.Z r ≤ sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsEqPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  wp_apply wp_sorter_Swap_raw x own R xs a pivot xa xp (by omega) (by omega)
    Hxa_lookup Hxp_lookup $$ [$Hsrt $Hxs] as Hxs
  (try wp_auto)
  ipersist a
  ipersist data
  ihave HI : peqInv own R a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold peqInv
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i j xi xj hb; word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact peq_init_min R xs _ _ _ xp xa Hxp_lookup Hxa_lookup ⟨by word, by word⟩ Hmin
  wp_for
  -- first inner loop: `for i <= j && !data.Less(a, i) { i++ }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv own R a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · unfold peqInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat i_val) as xi
      wp_apply wp_sorter_Less x own R xs1 a i_val xp xi (by word) (by word) Hpivot Hxi_lookup
        $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
      cases r
      · bool_if'
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
           fun h => by simpa using Hr.2 h⟩
      · bool_if'
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
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)
  -- second inner loop: `for i <= j && data.Less(a, j) { j-- }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv own R a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · unfold peqInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat j_val) as xj
      wp_apply wp_sorter_Less x own R xs1 a j_val xp xj (by word) (by word) Hpivot Hxj_lookup
        $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
      cases r
      · bool_if'
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
          fun _ => Or.inr ?_⟩
        intro xj' hxj'
        rw [Hxj_lookup] at hxj'; cases hxj'
        exact fun h => by simpa using Hr.2 h
      · bool_if'
        wp_auto
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
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)
  unfold peqInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  (try wp_auto)
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
    wp_apply wp_sorter_Swap_raw x own R xs1 i_val j_val xi xj (by word) (by word) Hxi_lookup
      Hxj_lookup $$ [$Hsrt $Hxs] as Hxs
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
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

end sort

end Perennial
end
