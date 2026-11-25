/-
The proof of `internal.reflectlite.rtype.Implements`.
-/
module

public import Perennial.Spec.internal.reflectlite.rtype__Implements
public import Perennial.Spec.internal.reflectlite.rtype__Kind
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

theorem internal.reflectlite.rtype.Implements.wp_proof
    (wp_rtype_Kind : internal.reflectlite.rtype.Kind.spec (GF := GF) (hG := hG))
    (wp_implements : internal.reflectlite.implements.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.rtype.Implements.spec (GF := GF) (hG := hG) :=
    @fun U elems _ _ W _ _ t ut _ _ _ kt hkt hi hn => by
  wp_start as #Hinit
  try wp_auto
  unfold go.tok
  wp_apply wp_rtype_Kind (T := U) 20 null internal.reflectlite.kindOf_interface
  try wp_auto
  wp_meths
  rw [show (interface.mkOk (go.PointerType U) #null : GoInterface) = go.tok U from rfl,
    show (interface.mkOk (go.PointerType t) #null : GoInterface) = go.tok t from rfl]
  wp_apply wp_implements.2 (T := U) (W := W) (V := t) kt hkt hi hn
  iapply HΦ
  itrivial

end proof

end Perennial
