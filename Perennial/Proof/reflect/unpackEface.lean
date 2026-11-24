/-
The proof of `reflect.unpackEface`.
-/
module

public import Perennial.Spec.reflect.unpackEface
public import Perennial.Spec.reflect.isModelRType
public import Perennial.Spec.reflect.isDirectIface
public import Perennial.Spec.internal.reflectcore.TokOf
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.Box

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

theorem reflect.unpackEface.wp_proof
    (wp_TokOf : internal.reflectcore.TokOf.spec (GF := GF) (hG := hG))
    (wp_isModelRType : reflect.isModelRType.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_isDirectIface : reflect.isDirectIface.spec (GF := GF) (hG := hG))
    (wp_Box : internal.reflectcore.Box.spec (GF := GF) (hG := hG)) :
    reflect.unpackEface.spec (GF := GF) (hG := hG) := by
  constructor
  · intro t u hu k n v hk ht hd
    wp_start as #Hinit
    wp_auto
    wp_apply wp_TokOf
    unfold go.tok
    wp_apply wp_isModelRType t null ht
    wp_apply wp_TypeKind k null hk
    wp_apply wp_isDirectIface n t null true hd
    iapply HΦ
    itrivial
  · intro V _ _ t u hu _ k n x hk ht hd hi
    wp_start as #Hinit
    wp_auto
    wp_apply wp_TokOf
    unfold go.tok
    wp_apply wp_isModelRType t null ht
    wp_apply wp_TypeKind k null hk
    wp_apply wp_isDirectIface n t null false hd
    wp_apply wp_Box x hi as %q Hq
    iapply HΦ
    iexact Hq

end proof

end Perennial
