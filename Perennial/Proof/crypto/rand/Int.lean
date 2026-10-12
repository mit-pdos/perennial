/-
The proof of `crypto/rand.Int`.
-/
module

public import Perennial.Spec.crypto.rand.Int
public import Perennial.Spec.math.big.NewInt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.rand.Assumptions]

theorem crypto.rand.Int.wp_proof
    (wp_NewInt : math.big.NewInt.spec (GF := GF) (hG := hG)) :
    crypto.rand.Int.spec (GF := GF) (hG := hG) := by
  intro rdr max mz Hmz
  wp_start as Hmax
  unfold math.big.ownInt
  icases Hmax with ⟨#HR, %x, %ws, Hp, Hws, %Hz, %Hnorm⟩
  -- `0 < mz < 2^63`: the sign is clear and the magnitude is one word, `mz`
  have Hneg : x.neg' = false := by
    cases h : x.neg'
    · rfl
    · simp only [h, ↓reduceIte] at Hz
      have := math.big.natValue_nonneg ws
      omega
  simp only [Hneg, Bool.false_eq_true, ↓reduceIte] at Hz
  have Hne : ws ≠ [] := by
    rintro rfl; simp only [math.big.natValue] at Hz; omega
  obtain ⟨m, rfl⟩ := math.big.natValue_one_word ws Hne Hnorm (by omega)
  have Hm : uint.Z m = mz := by simp only [math.big.natValue] at Hz; omega
  ihave %Hlen := ownSlice_len $$ Hws
  simp only [List.length_singleton] at Hlen
  wp_auto
  simp only [Hneg]
  wp_auto
  simp only [show x.abs'.len = W64 1 by word, decide_true, Bool.not_true]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index x.abs' (sint.Z (W64 0)) [m] (DFrac.own 1) m (by word) $$ [Hws]
    with Hws
  · iframe Hws; ipureintro; rfl
  have Hm0 : m ≠ W64 0 := by
    rintro rfl; revert Hm; simp only [show uint.Z (W64 0) = 0 from rfl]; omega
  simp only [decide_eq_false Hm0]
  wp_auto
  rw [decide_eq_false (show ¬ uint.Z (W64 (2 ^ 63)) ≤ uint.Z m by word)]
  wp_auto
  wp_apply wp_ArbitraryInt as %r _
  rw [if_neg (show ¬ uint.Z m = 0 by omega)]
  wp_apply wp_NewInt as %v Hv
  ispecialize HΦ $$ %v %(sint.Z (r % m))
  iapply HΦ
  isplitl [Hp Hws]
  · iexists x, [m]
    iframe
    ipureintro
    exact ⟨by simp only [Hneg, Bool.false_eq_true, ↓reduceIte, Hz], Hnorm⟩
  isplitl [Hv]
  · unfold math.big.ownInt
    icases Hv with ⟨%x', %ws', Hv, Hws', %Hv⟩
    iexists x', ws'
    iframe
    ipureintro
    exact Hv
  ipureintro
  have hm : 0 < m.toNat := by
    have : (0 : _root_.Int) < uint.Z m := by omega
    word
  have : (r % m).toNat < m.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hm
  constructor <;> word

end proof

end Perennial
