/-
The proof of `sort.SearchStrings`.
-/
module

public import Perennial.Spec.sort.SearchStrings
public import Perennial.Spec.sort.Search
public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.SearchStrings.wp_proof
    (wp_Search : sort.Search.spec (GF := GF) (hG := hG)) :
    sort.SearchStrings.spec (GF := GF) (hG := hG) := fun a x q xs => by
  -- (`fun`, not `intro`: see `sort.SearchInts.wp_proof`)
  wp_start as ⟨Ha, %Hsort⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Ha
  ipersist x
  ipersist a
  wp_pures
  rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
    fun x b => by rw [go.intoVal_unfold GoFunc]]
  wp_apply wp_Search _ _ (sort.searchStringsF x xs) iprop(a ↦*{q} xs) $$ [Ha]
  · iframe Ha
    isplitl []
    · ipureintro; omega
    isplitl []
    · unfold predImplements
      iintro %i
      wp_start as ⟨Ha, %Hbound⟩
      wp_auto
      list_elem xs (sint.nat i) as x_i
      simp only [Hbound.1, Hbound.2, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z i) xs q x_i Hbound.1 $$ [Ha] with Ha
      · iframe Ha; ipureintro; exact Hx_i_lookup
      iapply HΦ
      iframe Ha
      ipureintro
      unfold sort.searchStringsF
      rw [show (sint.Z i).toNat = sint.nat i from rfl, Hx_i_lookup]
    · ipureintro
      intro i j Hij Hfi
      list_elem xs i.toNat as x_i
      list_elem xs j.toNat as x_j
      rw [sort.searchStringsF_true _ _ _ _ Hx_i_lookup] at Hfi
      rw [sort.searchStringsF_true _ _ _ _ Hx_j_lookup]
      exact sort.goStringLe_trans Hfi (Hsort i.toNat j.toNat (by omega) _ _ Hx_i_lookup Hx_j_lookup)
  iintro %i ⟨Ha, %Hi_nn, %Hfound, %Hoob, %Hgt⟩
  wp_auto
  have Hlt_all : ∀ (j : Nat) x0, (j : Int) < sint.Z i → xs[j]? = some x0 → go.GoStringLt x0 x := by
    intro j x0 Hj Hget
    have Hj' := Hgt (j : Int) (by omega)
    rw [sort.searchStringsF_false _ _ _ _ (by simpa using Hget)] at Hj'
    exact Hj'
  have Hle_len : sint.Z i ≤ xs.length := by
    apply Classical.byContradiction
    intro hgt
    have := Hoob (fun k Hk => Hgt k (by word))
    have := Hlen.1
    word
  iapply HΦ
  iframe Ha
  isplitl []
  · ipureintro; exact ⟨Hi_nn, Hle_len⟩
  ipureintro
  refine ⟨Hlt_all, ?_⟩
  intro j xj Hj_bound Hget_j
  by_cases hin : sint.Z i < sint.Z a.len
  · have Hfound := Hfound hin
    list_elem xs (sint.nat i) as xi
    rw [sort.searchStringsF_true _ _ _ _ Hxi_lookup] at Hfound
    by_cases hij : sint.nat i = j
    · subst hij
      rw [Hxi_lookup] at Hget_j
      cases Hget_j
      exact Hfound
    · exact sort.goStringLe_trans Hfound (Hsort (sint.nat i) j (by word) _ _ Hxi_lookup Hget_j)
  · have := lookup_lt_Some Hget_j
    have := Hlen.1
    word

end proof

end Perennial
