/-
The proof of `reflect.Value.Interface`.
-/
module

public import Perennial.Spec.reflect.Value__Interface
public import Perennial.Spec.reflect.flag__kind
public import Perennial.Spec.reflect.isDirectIface

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.Value.Interface.wp_proof
    (wp_flag_kind : reflect.flag.kind.spec (GF := GF) (hG := hG))
    (wp_isDirectIface : reflect.isDirectIface.spec (GF := GF) (hG := hG)) :
    reflect.Value.Interface.spec (GF := GF) (hG := hG) := fun v T l htyp hptr hk hf => by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  have h0 : v.flag' ≠ W64 0 := by intro h; rw [h] at hk; simp at hk
  have hro : v.flag' &&& W64 96 = W64 0 := by
    rw [show W64 96 = W64 736 &&& W64 96 by decide, ← BitVec.and_assoc, hf]; simp
  have hm : v.flag' &&& W64 512 = W64 0 := by
    rw [show W64 512 = W64 736 &&& W64 512 by decide, ← BitVec.and_assoc, hf]; simp
  have hi : v.flag' &&& W64 128 = W64 0 := by
    rw [show W64 128 = W64 736 &&& W64 128 by decide, ← BitVec.and_assoc, hf]; simp
  wp_start as #Hinit
  wp_auto
  wp_func_call; wp_call
  wp_auto
  wp_if_destruct <;> try (first | exact absurd Hif ‹_› | exact absurd ‹_› Hif)
  wp_if_destruct <;> try (first | exact absurd Hif ‹_› | exact absurd ‹_› Hif)
  wp_if_destruct <;> try (first | exact absurd Hif ‹_› | exact absurd ‹_› Hif)
  wp_method_call; wp_call
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_flag_kind
  rw [hk]
  wp_auto
  wp_func_call; wp_call
  wp_auto
  wp_func_call; wp_call
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [htyp]
  unfold go.tok
  wp_apply wp_isDirectIface 1 (go.PointerType T) null true
    (reflect.directIfaceN_of_kind (u := go.PointerType T) (k := 22) 0 (by simp [go.kindOf]) (by omega)
      (by omega))
  simp only [hi, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  rw [hptr]
  iapply HΦ
  itrivial

end proof

end Perennial
