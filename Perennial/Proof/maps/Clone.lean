/-
The proof of `maps.Clone` (over the model of `clone`, `TrustedCode/maps.lean`).
-/
module

public import Perennial.Spec.maps.Clone

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std map

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

theorem maps.Clone.wp_proof :
    maps.Clone.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ T Kt Vt _
  constructor
  · intro m dq M
    wp_start as Hm
    ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_func_call
    unfold maps.clone.impl
    wp_pure
    wp_apply wp_map_clone $$ Hm with %m' Hm
    iapply HΦ $$ Hm
  · wp_start
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
