/-
The proof of `internal.reflectlite.packEface`.
-/
module

public import Perennial.Spec.internal.reflectlite.packEface
public import Perennial.Spec.internal.reflectlite.isDirectIface
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
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.packEface.wp_proof
    (wp_isDirectIface : internal.reflectlite.isDirectIface.spec (GF := GF) (hG := hG))
    (wp_Load : internal.reflectcore.Load.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.packEface.spec (GF := GF) (hG := hG) :=
    @fun W _ _ t ut _ _ kt xv x hkt hi hn => by
  unfold internal.reflectlite.valueOfRepr
  have hb := internal.reflectlite.flag_bits kt (internal.reflectlite.kindOf_lt hkt)
    (internal.reflectlite.kindOf_pos hkt)
  obtain ⟨hb0, hb0i, hbk, hbki, hbi, hbii, hbro, hbroi, -⟩ := hb
  wp_start as Hx
  icases Hx with (⟨%hd, %hxv⟩ | ⟨%q, ⟨%hd, %hxv⟩, Hq⟩)
  · obtain ⟨n, hd⟩ := hd
    subst hxv
    try wp_auto
    wp_meths
    unfold go.tok
    wp_apply wp_isDirectIface n t null true hd
    try simp only [hbi]
    try wp_auto
    iapply HΦ
    ileft
    ipureintro
    refine ⟨⟨n, hd⟩, ?_⟩
    first | rfl | trivial
  · obtain ⟨n, hd⟩ := hd
    subst hxv
    try wp_auto
    wp_meths
    unfold go.tok
    wp_apply wp_isDirectIface n t null false hd
    try simp only [hbii]
    try wp_auto
    wp_apply wp_Load.1 q (DFrac.own 1) x hi hn $$ [$Hq] as Hq
    iapply HΦ
    iright
    iexists q
    iframe
    ipureintro
    refine ⟨⟨n, hd⟩, ?_⟩
    first | rfl | trivial

end proof

end Perennial
