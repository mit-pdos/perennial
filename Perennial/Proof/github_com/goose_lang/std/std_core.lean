/-
Specs for
`github.com/goose-lang/std/std_core` (overflow checks, `Shuffle`,
`Permutation`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.github_com.goose_lang.std.std_core
import Perennial.GeneratedProof.github_com.goose_lang.std.std_core
import Perennial.Proof.github_com.goose_lang.primitive

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.goose_lang.std.std_core

theorem umod_succ_bound (x i : w64) (hi : 0 ≤ sint.Z i) :
    0 ≤ sint.Z (x % (i + W64 1)) ∧ sint.Z (x % (i + W64 1)) ≤ sint.Z i := by
  have h0 : (i + W64 1).toNat ≠ 0 := by word
  have h2 : (x % (i + W64 1)).toNat < (i + W64 1).toNat := by
    rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h0)
  constructor <;> word

theorem sint_eq_uint (x : w64) (h : 0 ≤ sint.Z x) : sint.Z x = uint.Z x := by word

theorem sint_succ_of_lt (i n : w64) (Hif : uint.Z i < uint.Z n) (Hi : 0 ≤ sint.Z i)
    (Hn : 0 ≤ sint.Z n) : sint.Z (i + W64 1) = sint.Z i + 1 := by word

theorem W64_sint (x : w64) : W64 (sint.Z x) = x := by simp [W64, sint.Z]

theorem seqZ_plus_1 (n m : Int) (h : 0 ≤ m) : seqZ n (m + 1) = seqZ n m ++ [n + m] := by
  unfold seqZ
  rw [show (m + 1).toNat = m.toNat + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 2
  omega

theorem perm_step (k m : Nat) (h : k < m) :
    (((seqZ 0 k).map (fun z => W64 z)) ++ List.replicate (m - k) (W64 0)).set k (W64 k) =
      ((seqZ 0 (k + 1)).map (fun z => W64 z)) ++ List.replicate (m - (k + 1)) (W64 0) := by
  rw [show m - k = (m - (k + 1)) + 1 by omega, List.replicate_succ]
  rw [list_set_middle _ _ _ _ _ (by simp [length_seqZ])]
  rw [seqZ_plus_1 _ _ (by omega)]
  simp

/-- Local copy of `slices_proof` `slice_index_if`: discharge the bounds check of
an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.goose_lang.std.std_core get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hprim⟩
  iframe Hown
  is_pkg_init_finish

theorem wp_SumNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! SumNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x + y) = uint.Z x + uint.Z y)); True }} := by
  wp_start as _
  wp_auto
  have h : (uint.Z x ≤ uint.Z (x + y)) ↔ (uint.Z (x + y) = uint.Z x + uint.Z y) := by
    have := sum_overflow_check x y
    constructor <;> intro <;> word
  rw [decide_eq_decide.mpr h]
  iapply HΦ
  itrivial

theorem wp_SumAssumeNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! SumAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x + y); ⌜uint.Z (x + y) = uint.Z x + uint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_SumNoOverflow
  wp_apply github_com.goose_lang.primitive.wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

theorem wp_MulNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x * y) = uint.Z x * uint.Z y)); True }} := by
  wp_start as _
  wp_auto
  wp_if_destruct
  · rw [decide_eq_true (by simp [uint.Z])]
    iapply HΦ; itrivial
  · have Hx := Hif
    wp_if_destruct
    · rw [decide_eq_true (by simp [uint.Z])]
      iapply HΦ; itrivial
    · have hx : uint.Z x ≠ 0 := fun h => Hx (by word)
      have h : (uint.Z x ≤ uint.Z (W64 18446744073709551615 / y)) ↔
          (uint.Z (x * y) = uint.Z x * uint.Z y) := by
        have hy : uint.Z y ≠ 0 := fun h => Hif (by word)
        have hc := mul_overflow_check_correct x y hx hy
        rw [word.unsigned_mul, word.unsigned_divu, show uint.Z (W64 18446744073709551615) = 2 ^ 64 - 1 from rfl]
        have ha := uint_Z_nonneg x
        have hb := uint_Z_nonneg y
        generalize uint.Z x = a at *
        generalize uint.Z y = b at *
        have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
        generalize a * b = P at *
        generalize (2 ^ 64 - 1) / b = Q at *
        constructor
        · intro h1; exact Int.emod_eq_of_lt hab (by omega)
        · intro h1
          have : P < 2 ^ 64 := by
            have := Int.emod_lt_of_pos P (show (0:Int) < 2 ^ 64 by decide); omega
          omega
      rw [decide_eq_decide.mpr h]
      iapply HΦ; itrivial

theorem wp_MulAssumeNoOverflow (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x * y); ⌜uint.Z (x * y) = uint.Z x * uint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_MulNoOverflow
  wp_apply github_com.goose_lang.primitive.wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

theorem wp_Shuffle (s : GoSlice) (xs : List w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core ∗ s ↦* xs }}
      (App (Val (@! Shuffle)) (Val #s))
    {{ (xs' : List w64), RET #(); ⌜xs ≡ₚ xs'⌝ ∗ s ↦* xs' }} := by
  wp_start as Hs
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_if_destruct
  · have hnil : xs = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    subst hnil
    iapply HΦ
    iframe Hs
    ipureintro; exact List.Perm.refl _
  ihave HI : (∃ (i : w64) (xs' : List w64),
      "i" ∷ i_ptr ↦ i ∗ "Hs" ∷ s ↦* xs' ∗
      "%HI" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len⌝ ∗
      "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ : IProp GF) $$ [i Hs]
  · iexists _, xs
    iframe
    ipureintro
    refine ⟨⟨?_, ?_⟩, List.Perm.refl _⟩ <;> word
  wp_for HI
  have hlen' := Hperm.length_eq
  wp_if_destruct
  · wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    have hj := umod_succ_bound x i HI.1
    list_elem xs' (sint.nat i) as x_i
    list_elem xs' (sint.nat (x % (i + W64 1))) as x_j
    slice_index_if
    wp_apply wp_load_slice_index s (sint.Z i) xs' _ x_i HI.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hx_i_lookup
    slice_index_if
    wp_apply wp_load_slice_index s (sint.Z (x % (i + W64 1))) xs' _ x_j hj.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hx_j_lookup
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index s (sint.Z i) xs' x_j $$ [Hs] with Hs
    · iframe Hs; ipureintro; simp only [sint.nat, sint.Z] at *; omega
    slice_index_if
    wp_pures
    wp_apply wp_store_slice_index s (sint.Z (x % (i + W64 1))) _ x_i $$ [Hs] with Hs
    · iframe Hs; ipureintro; simp only [List.length_set]; simp only [sint.nat, sint.Z] at *; omega
    wp_for_post
    iframe
    iexists (i - W64 1), _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    exact Hperm.trans (List.Perm.symm (Permutation_insert_swap xs' _ _ _ _ Hx_i_lookup Hx_j_lookup))
  · iapply HΦ $$ [Hs]
    iframe Hs
    ipureintro; exact Hperm

theorem wp_Permutation (n : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core ∗ ⌜0 ≤ sint.Z n⌝ }}
      (App (Val (@! Permutation)) (Val #n))
    {{ (xs : List w64) (s : GoSlice), RET #s;
        ⌜xs ≡ₚ (seqZ 0 (sint.Z n)).map (fun z => W64 z)⌝ ∗ s ↦* xs }} := by
  wp_start as %Hnz
  wp_auto
  wp_apply wp_slice_make2 (V := w64) n $$ [] as %s ⟨Hs, -⟩
  · ipureintro; exact Hnz
  have hnu := sint_eq_uint n Hnz
  simp only [show (zero_val w64 : w64) = W64 0 from rfl]
  ihave HI : (∃ (i : w64),
      "Hs" ∷ s ↦* (((seqZ 0 (sint.Z i)).map (fun z => W64 z)) ++
        List.replicate (sint.nat n - sint.nat i) (W64 0)) ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z n⌝ : IProp GF) $$ [i Hs]
  · iexists (W64 0)
    simp only [seqZ_nil 0 (sint.Z (W64 0)) (by decide), List.map_nil, List.nil_append,
      show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; exact ⟨by decide, Hnz⟩
  wp_for HI
  have hiu := sint_eq_uint i Hi.1
  by_cases Hif : uint.Z i < uint.Z n
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    have hlt : sint.nat i < sint.nat n := by simp only [sint.nat, sint.Z] at *; omega
    have hsl : sint.Z i < sint.Z s.len := by
      simp only [List.length_append, List.length_map, length_seqZ, List.length_replicate] at Hlen
      simp only [sint.nat, sint.Z] at *; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hsl⟩)]
    wp_pures
    wp_apply wp_store_slice_index s (sint.Z i) _ i $$ [Hs] with Hs
    · iframe Hs; ipureintro; simp [length_seqZ]; simp only [sint.nat, sint.Z] at *; omega
    wp_for_post
    iframe
    iexists (i + W64 1)
    have hi1 := sint_succ_of_lt i n Hif Hi.1 Hnz
    have hstep := perm_step (sint.nat i) (sint.nat n) hlt
    have e1 : ((sint.nat i : Nat) : Int) = sint.Z i := by simp only [sint.nat, sint.Z] at *; omega
    have e2 : sint.nat i + 1 = sint.nat (i + W64 1) := by simp only [sint.nat, sint.Z] at *; omega
    rw [e1, W64_sint, e2, ← hi1] at hstep
    rw [show (sint.Z i).toNat = sint.nat i from rfl, hstep]
    iframe
    ipureintro; omega
  · simp only [Hif, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply wp_Shuffle s _ $$ [$Hs] as %xs' ⟨%Hperm, Hs⟩
    iapply HΦ
    iframe Hs
    ipureintro
    have hin : i = n := by
      apply BitVec.eq_of_toNat_eq; simp only [uint.Z, sint.Z] at *; omega
    subst hin
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at Hperm
    exact Hperm.symm

end wps

end github_com.goose_lang.std.std_core

end Perennial
end
