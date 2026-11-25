/-
The proof of `internal.reflectlite.Value.IsNil`.
-/
module

public import Perennial.Spec.internal.reflectlite.Value__IsNil
public import Perennial.Spec.internal.reflectlite.flag__kind
public import Perennial.Spec.internal.reflectcore.EqNilAt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.Value.IsNil.wp_proof
    (wp_flag_kind : internal.reflectlite.flag.kind.spec (GF := GF) (hG := hG))
    (wp_EqNilAt : internal.reflectcore.EqNilAt.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.Value.IsNil.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  intro v t e _ _ l hk hi hptr
  wp_start as #Hinit
  wp_auto
  wp_method_call; wp_call
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_flag_kind
  rw [hk, internal.reflectlite.u8_lit22]
  wp_auto
  simp only [hi, decide_true, Bool.not_true]
  wp_auto
  rw [hptr]
  wp_apply wp_EqNilAt.1 l
  iapply HΦ
  itrivial

end proof

end Perennial
