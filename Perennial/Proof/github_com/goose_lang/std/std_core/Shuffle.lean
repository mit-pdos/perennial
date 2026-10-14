/-
The proof of `github.com/goose-lang/std/std_core.Shuffle`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.Shuffle
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

/-- Local copy of `slice_index_if` (`Perennial/Proof/slices/SortBasics.lean`): discharge the
bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

theorem github_com.goose_lang.std.std_core.Shuffle.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.std_core.Shuffle.spec (GF := GF) (hG := hG) := fun s xs => by
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
  · wp_apply wp_RandomUint64 as %x _
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

end proof

end Perennial
