/-
The proof of `internal.reflectlite.rtype.AssignableTo`.
-/
module

public import Perennial.Spec.internal.reflectlite.rtype__AssignableTo
public import Perennial.Spec.internal.reflectlite.directlyAssignable
public import Perennial.Spec.internal.reflectlite.implements

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

theorem internal.reflectlite.rtype.AssignableTo.wp_proof
    (wp_directlyAssignable : internal.reflectlite.directlyAssignable.spec (GF := GF) (hG := hG))
    (wp_implements : internal.reflectlite.implements.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.rtype.AssignableTo.spec (GF := GF) (hG := hG) := by
  constructor
  · intro T V uT uV _ _ _ _ kT kV hkT hkV h20 hid hne
    wp_start as #Hinit
    try wp_auto
    wp_meths
    wp_apply wp_directlyAssignable kT kV hkT hkV hid hne
    by_cases hTV : T = V
    · simp only [hTV, decide_true]
      try wp_auto
      iapply HΦ
      itrivial
    · simp only [hTV, decide_false]
      try wp_auto
      wp_apply wp_implements.1 (T := T) kT (go.tok V) hkT h20
      iapply HΦ
      itrivial
  · intro T elems _ _ W _ _ V uV _ _ _ kV hkV hi hn
    have hUT : _root_.Perennial.underlying T = go.InterfaceType elems := go.is_underlying
    have hUV : _root_.Perennial.underlying V = uV := go.is_underlying
    have hkT : go.kindOf (go.InterfaceType elems) = some 20 := internal.reflectlite.kindOf_interface
    have hTV : T ≠ V := by
      intro h; subst h; rw [hUT] at hUV; subst hUV; simp [go.isInterfaceType] at hi
    have h20 := internal.reflectlite.kindOf_ne_20 hkV hi
    wp_start as #Hinit
    try wp_auto
    wp_meths
    wp_apply wp_directlyAssignable (T := T) (V := V) 20 kV hkT hkV (fun h => absurd h hTV)
      (fun _ => Or.inr (Or.inl (Ne.symm h20)))
    simp only [hTV, decide_false]
    try wp_auto
    wp_apply wp_implements.2 (T := T) (W := W) (V := V) kV hkV hi hn
    iapply HΦ
    itrivial

end proof

end Perennial
