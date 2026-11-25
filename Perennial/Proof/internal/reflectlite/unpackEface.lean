/-
The proof of `internal.reflectlite.unpackEface`.
-/
module

public import Perennial.Spec.internal.reflectlite.unpackEface
public import Perennial.Spec.internal.reflectcore.TokOf
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectlite.isDirectIface
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
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.unpackEface.wp_proof
    (wp_TokOf : internal.reflectcore.TokOf.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_isDirectIface : internal.reflectlite.isDirectIface.spec (GF := GF) (hG := hG))
    (wp_Box : internal.reflectcore.Box.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.unpackEface.spec (GF := GF) (hG := hG) := by
  intro V _ _ t u hu _ k n b x hk hi hd
  unfold internal.reflectlite.valueOfRepr
  have hU : GoSemanticsFunctions.underlying t = u := go.is_underlying
  haveI : go.NotLayoutModelled t := ⟨reflect.notLayoutModelled_of_directIfaceN hd⟩
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TokOf
  unfold go.tok
  wp_apply wp_TypeKind k null hk
  wp_apply wp_isDirectIface n t null b hd
  cases b
  · try wp_auto
    wp_apply wp_Box x hi as %q Hq
    iapply HΦ
    iright
    iexists q
    iframe
    ipureintro
    refine ⟨⟨n, hd⟩, ?_⟩
    first | rfl | trivial
  · wp_auto
    iapply HΦ
    ileft
    ipureintro
    refine ⟨⟨n, hd⟩, ?_⟩
    first | rfl | trivial

end proof

end Perennial
