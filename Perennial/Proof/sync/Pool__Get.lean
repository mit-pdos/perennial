/-
The proof of `sync.(*Pool).Get`, whose model (`goose/model/overlay/sync/pool.go`) takes an
arbitrary element of the pool's state (`poolModelOf`) or nothing, and calls `New` when it has
`nil`.
-/
module

public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.poolModelOf
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Pool.Get.wp_proof
    (wp_poolModelOf : sync.poolModelOf.spec (GF := GF) (hG := hG))
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    sync.Pool.Get.spec (GF := GF) (hG := hG) := by
  intro p f R P
  wp_start as ⟨#His, HR⟩
  wp_auto
  wp_apply wp_poolModelOf p f R P $$ [$His] as %s #Hs
  simp only [sync.isPool_unseal, sync.isPoolDef, sync.isPoolModel_unseal, sync.isPoolModelDef]
  iNamed His
  wp_apply wp_Mutex_Lock $$ [$Hs] as ⟨Hlocked, Hi⟩
  unfold sync.poolInv
  iNamed Hi
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  wp_if_destruct
  · -- the pool is empty
    wp_apply wp_Mutex_Unlock $$ [$Hs $Hlocked items Hsl Hcap HP]
    · iexists sl, xs; iframe
    by_cases hf : f = func.nil
    · rw [decide_eq_true hf]
      wp_auto
      iapply HΦ
      iframe
      iright; ipureintro; exact ⟨hf, rfl⟩
    · rw [decide_eq_false hf]
      unfold sync.newSpec
      icases HNew with (%h | #HNew)
      · exact absurd h hf
      wp_auto
      wp_apply HNew $$ [$HR] as %y ⟨Hy, HR⟩
      iapply HΦ
      iframe
  · have hlen0 : ¬ sl.len = W64 0 := ‹_›
    wp_apply wp_Choose as %b _
    cases b
    · -- take an element
      wp_auto
      wp_apply wp_ChooseUint64 as %j _
      rw [ite_eq_right (show ¬ uint.Z sl.len = 0 by word)]
      have hn : 0 < xs.length := by word
      have hmod : uint.Z (j % sl.len) < uint.Z sl.len := by
        have h0 : 0 < sl.len.toNat := by
          rcases Nat.eq_zero_or_pos sl.len.toNat with h | h
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hlen0
          · exact h
        have := Nat.mod_lt j.toNat h0
        word
      have hi : 0 ≤ sint.Z (j % sl.len) ∧ sint.Z (j % sl.len) < sint.Z sl.len := by word
      have hk : (sint.Z (j % sl.len)).toNat < xs.length := by word
      have hlast : (sint.Z (sl.len - W64 1)).toNat = xs.length - 1 := by word
      obtain ⟨x0, Hx0⟩ : ∃ x0, xs[(sint.Z (j % sl.len)).toNat]? = some x0 :=
        ⟨_, List.getElem?_eq_getElem hk⟩
      obtain ⟨y, Hy⟩ : ∃ y, xs[(sint.Z (sl.len - W64 1)).toNat]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_auto
      rw [ite_eq_left hi]
      wp_apply wp_load_slice_index sl (sint.Z (j % sl.len)) xs _ x0 hi.1 $$ [Hsl] with Hsl
      · iframe; ipureintro; exact Hx0
      rw [ite_eq_left (show 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len by word)]
      wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) xs _ y (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; exact Hy
      wp_auto
      rw [ite_eq_left hi]
      wp_apply wp_store_slice_index sl (sint.Z (j % sl.len)) xs y $$ [Hsl] with Hsl
      · iframe; ipureintro; word
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
        sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap by word)]
      icases ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl
        (xs.set (sint.Z (j % sl.len)).toNat y) (by word) $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
      · iframe
      wp_auto
      have hperm : (subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1))
          (xs.set (sint.Z (j % sl.len)).toNat y) ++ [x0]).Perm xs := by
        have h := sync.swapRemove_perm xs _ hk
        rw [hlast] at Hy
        have hy : xs[xs.length - 1]'(by omega) = y := by
          rw [List.getElem?_eq_getElem (by omega)] at Hy; exact Option.some.inj Hy
        have hx : xs[(sint.Z (j % sl.len)).toNat] = x0 := by
          rw [List.getElem?_eq_getElem hk] at Hx0; exact Option.some.inj Hx0
        rw [hy, hx] at h
        rw [show sint.nat (sl.len - W64 1) = xs.length - 1 by word,
          show sint.nat (W64 0) = 0 from rfl]
        simpa [subslice] using h
      ihave HP := (BigSepL.bigSepL_perm hperm).2 $$ HP
      icases BigSepL.bigSepL_snoc.1 $$ HP with ⟨HP, Hx0⟩
      wp_apply wp_Mutex_Unlock $$ [$Hs $Hlocked items Hsl Hcap HP]
      · iexists _, _; iframe
      cases x0 with
      | ok i =>
        wp_auto
        iapply HΦ
        iframe
      | nil =>
        wp_auto
        by_cases hf : f = func.nil
        · rw [decide_eq_true hf]
          wp_auto
          iapply HΦ
          iframe
        · rw [decide_eq_false hf]
          unfold sync.newSpec
          icases HNew with (%h | #HNew)
          · exact absurd h hf
          wp_auto
          wp_apply HNew $$ [$HR] as %y ⟨Hy, HR⟩
          iapply HΦ
          iframe
    · -- `Choose` ignores the pool
      wp_auto
      wp_apply wp_Mutex_Unlock $$ [$Hs $Hlocked items Hsl Hcap HP]
      · iexists sl, xs; iframe
      by_cases hf : f = func.nil
      · rw [decide_eq_true hf]
        wp_auto
        iapply HΦ
        iframe
        iright; ipureintro; exact ⟨hf, rfl⟩
      · rw [decide_eq_false hf]
        unfold sync.newSpec
        icases HNew with (%h | #HNew)
        · exact absurd h hf
        wp_auto
        wp_apply HNew $$ [$HR] as %y ⟨Hy, HR⟩
        iapply HΦ
        iframe

end proof

end Perennial
