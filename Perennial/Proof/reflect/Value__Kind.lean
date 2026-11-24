/-
The proof of `reflect.Value.Kind`.
-/
module

public import Perennial.Spec.reflect.Value__Kind
public import Perennial.Spec.reflect.flag__kind

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

theorem reflect.Value.Kind.wp_proof
    (wp_flag_kind : reflect.flag.kind.spec (GF := GF) (hG := hG)) :
    reflect.Value.Kind.spec (GF := GF) (hG := hG) := fun v => by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  wp_start as #Hinit
  wp_auto
  wp_method_call; wp_call
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_flag_kind
  iapply HΦ
  itrivial

end proof

end Perennial
