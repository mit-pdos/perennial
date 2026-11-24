/-
The proof of `runtime.callers` (trusted: a call of its translated model `callersModel`,
`goose/model/overlay/runtime/traceback.go`).
-/
module

public import Perennial.Spec.runtime.callers_
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.callers.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    runtime.callers.spec (GF := GF) (hG := hG) := fun skip s xs => by
  wp_start as Hs
  -- `callers.impl` (trusted) calls the translated model `callersModel`
  try rw [show (go!"runtime.callersModel" : GoString) = runtime.callersModel from rfl]
  wp_func_call
  wp_call
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  ihave HI : iprop(∃ (n : w64) (ys : List w64),
      "n" ∷ n_ptr ↦ n ∗
      "Hs" ∷ s ↦* ys ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ ys.length = xs.length ∧
        ys.drop (sint.nat n) = xs.drop (sint.nat n)⌝) $$ [n Hs]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, rfl, rfl⟩
  wp_for HI
  ihave %Hlen' := ownSlice_len $$ Hs
  wp_if_destruct
  · wp_apply wp_Choose as %c -
    rcases c with _ | _ <;> simp only [intoVal_eq_iff, decide_false, decide_true,
      Bool.false_eq_true, ↓reduceIte]
    · wp_auto
      iapply HΦ
      iexists ys
      iframe
      ipureintro; exact Hn
    · wp_auto
      wp_apply wp_ChooseUint64 as %v -
      have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif⟩
      have hsl : (ys.length : Int) = sint.Z s.len := by
        rw [Hlen'.1]; show ((sint.Z s.len).toNat : Int) = _; omega
      have hxl : (xs.length : Int) = sint.Z s.len := by
        rw [Hlen.1]; show ((sint.Z s.len).toNat : Int) = _; omega
      rw [ite_eq_left hb]
      wp_apply wp_store_slice_index s (sint.Z n) ys v $$ [Hs] as Hs
      · iframe; ipureintro; omega
      wp_for_post
      have hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      have hk : sint.nat (n + W64 1) = sint.nat n + 1 := by
        show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
        omega
      have hk' : (sint.nat (n + W64 1) : Int) = sint.Z n + 1 := by
        show ((sint.Z (n + W64 1)).toNat : Int) = _
        omega
      iframe
      iexists (n + W64 1), (ys.set (sint.Z n).toNat v)
      iframe
      ipureintro
      refine ⟨by omega, by omega, by simp [Hn.2.2.1], ?_⟩
      rw [hk, List.drop_set_of_lt (by show (sint.Z n).toNat < (sint.Z n).toNat + 1; omega),
        ← List.drop_drop, ← List.drop_drop, Hn.2.2.2]
  · iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hn

end proof

end Perennial
