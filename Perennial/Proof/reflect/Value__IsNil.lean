/-
The proof of `reflect.Value.IsNil`.
-/
module

public import Perennial.Spec.reflect.Value__IsNil
public import Perennial.Spec.reflect.flag__kind
public import Perennial.Spec.internal.reflectcore.EqNilAt
public import Perennial.Spec.internal.reflectcore.Load

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

theorem reflect.Value.IsNil.wp_proof
    (wp_flag_kind : reflect.flag.kind.spec (GF := GF) (hG := hG))
    (wp_EqNilAt : internal.reflectcore.EqNilAt.spec (GF := GF) (hG := hG))
    (wp_Load : internal.reflectcore.Load.spec (GF := GF) (hG := hG)) :
    reflect.Value.IsNil.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v t e _ l hk hf hptr
    have hm : v.flag' &&& W64 512 = W64 0 := by
      rw [show W64 512 = W64 640 &&& W64 512 by decide, ← BitVec.and_assoc, hf]; simp
    have hi : v.flag' &&& W64 128 = W64 0 := by
      rw [show W64 128 = W64 640 &&& W64 128 by decide, ← BitVec.and_assoc, hf]; simp
    wp_start as #Hinit
    wp_auto
    wp_method_call; wp_call
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_flag_kind
    rw [hk]
    wp_auto
    simp only [hm, decide_true, Bool.not_true]
    wp_auto
    simp only [hi, decide_true, Bool.not_true]
    wp_auto
    rw [hptr]
    wp_apply wp_EqNilAt.1 l
    iapply HΦ
    itrivial
  · intro v t e _ q dq s hk hptr
    wp_start as Hq
    wp_auto
    wp_method_call; wp_call
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_flag_kind
    rw [hk]
    wp_auto
    rw [hptr]
    wp_apply wp_Load.1 q dq s rfl rfl $$ [$Hq] as Hq
    wp_apply wp_EqNilAt.2.1 s
    iapply HΦ
    iexact Hq
  · intro v Φ hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨h18, h19, h20, h21, h22, h23, h26⟩ := hk
    iintro ⟨#Hinit, HΦ⟩
    wp_method_call; wp_call
    wp_auto
    wp_method_call; wp_call
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_flag_kind
    repeat (first
      | (simp only [decide_eq_false h18, decide_eq_false h19, decide_eq_false h20,
          decide_eq_false h21, decide_eq_false h22, decide_eq_false h23, decide_eq_false h26]
         wp_auto)
      | wp_auto)
    wp_method_call; wp_call
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_flag_kind
    wp_alloc l as Hl
    wp_auto
    wp_apply wp_panic
    iapply HΦ
    iexact Hl

end proof

end Perennial
