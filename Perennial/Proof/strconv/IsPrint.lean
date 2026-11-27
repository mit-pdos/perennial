/-
The proof of `strconv.IsPrint`.
-/
module

public import Perennial.Spec.strconv.IsPrint
public import Perennial.Spec.strconv.bsearch

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.IsPrint.wp_proof (wp_bsearch : strconv.bsearch.spec (GF := GF) (hG := hG)) :
    strconv.IsPrint.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hpkg
  ihave #Hinit := strconv.isInit_access $$ Hpkg
  iNamed Hinit
  iunfold strconv.tableVar at HisPrint16 HisNotPrint16 HisPrint32 HisNotPrint32
  icases HisPrint16 with ⟨%p16, %xp16, #Gp16, #Sp16, %Lp16⟩
  icases HisNotPrint16 with ⟨%n16, %xn16, #Gn16, #Sn16, %Ln16⟩
  icases HisPrint32 with ⟨%p32, %xp32, #Gp32, #Sp32, %Lp32⟩
  icases HisNotPrint32 with ⟨%n32, %xn32, #Gn32, #Sn32, %Ln32⟩
  wp_auto
  wp_if_destruct
  · repeat' (first | wp_if_destruct | wp_auto)
    all_goals (iapply HΦ; itrivial)
  ihave %Hp16 := ownSlice_len _ _ _ $$ Sp16
  ihave %Hp32 := ownSlice_len _ _ _ $$ Sp32
  have hp16 : sint.Z p16.len = 424 := by
    obtain ⟨h1, h2⟩ := Hp16; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hp32 : sint.Z p32.len = 508 := by
    obtain ⟨h1, h2⟩ := Hp32; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  repeat' (first | wp_if_destruct | wp_auto)
  · wp_apply wp_bsearch.1 p16 xp16 _ DFrac.discard $$ [$Sp16] as %i %found ⟨-, %Hi⟩
    wp_if_destruct
    · iapply HΦ; itrivial
    have hidx := strconv.isPrint_idx i 424 (Or.inl rfl) Hi.1 (by omega)
    rw [ite_eq_left (by omega)]
    obtain ⟨x0, hx0⟩ : ∃ x, xp16[(sint.Z (i &&& ~~~W64 1)).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x0 (by omega) $$ [$Sp16] as -
    · ipureintro; exact hx0
    wp_if_destruct
    · iapply HΦ; itrivial
    rw [ite_eq_left (by omega)]
    obtain ⟨x1, hx1⟩ : ∃ x, xp16[(sint.Z (i ||| W64 1)).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x1 (by omega) $$ [$Sp16] as -
    · ipureintro; exact hx1
    wp_if_destruct
    · iapply HΦ; itrivial
    wp_apply wp_bsearch.1 n16 xn16 _ DFrac.discard $$ [$Sn16] as %j %found' -
    iapply HΦ; itrivial
  all_goals (
    wp_apply wp_bsearch.2 p32 xp32 _ DFrac.discard $$ [$Sp32] as %i %found ⟨-, %Hi⟩
    wp_if_destruct
    · iapply HΦ; itrivial
    have hidx := strconv.isPrint_idx i 508 (Or.inr rfl) Hi.1 (by omega)
    rw [ite_eq_left (by omega)]
    obtain ⟨x0, hx0⟩ : ∃ x, xp32[(sint.Z (i &&& ~~~W64 1)).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x0 (by omega) $$ [$Sp32] as -
    · ipureintro; exact hx0
    wp_if_destruct
    · iapply HΦ; itrivial
    rw [ite_eq_left (by omega)]
    obtain ⟨x1, hx1⟩ : ∃ x, xp32[(sint.Z (i ||| W64 1)).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x1 (by omega) $$ [$Sp32] as -
    · ipureintro; exact hx1
    wp_if_destruct
    · iapply HΦ; itrivial
    wp_if_destruct
    · iapply HΦ; itrivial
    wp_apply wp_bsearch.1 n32 xn32 _ DFrac.discard $$ [$Sn32] as %j %found' -
    iapply HΦ; itrivial)

end proof

end Perennial
