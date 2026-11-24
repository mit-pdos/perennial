/-
The proof of `internal.reflectlite.Value.Set`.
-/
module

public import Perennial.Spec.internal.reflectlite.Value__Set
public import Perennial.Spec.internal.reflectlite.Value__assignTo
public import Perennial.Spec.internal.reflectlite.flag__kind
public import Perennial.Spec.internal.reflectcore.Load
public import Perennial.Spec.internal.reflectcore.Store

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

theorem internal.reflectlite.Value.Set.wp_proof
    (wp_flag_kind : internal.reflectlite.flag.kind.spec (GF := GF) (hG := hG))
    (wp_assignTo : internal.reflectlite.Value.assignTo.spec (GF := GF) (hG := hG))
    (wp_Load : internal.reflectcore.Load.spec (GF := GF) (hG := hG))
    (wp_Store : internal.reflectcore.Store.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.Value.Set.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  constructor
  · intro V _ _ T uT _ _ kT l w y xv hkT hi hn hid
    have hlt := internal.reflectlite.kindOf_lt hkT
    have h20 := internal.reflectlite.kindOf_ne_20 hkT hi
    have hk20 := internal.reflectlite.kne_20 kT hlt h20
    have hku := internal.reflectlite.kind_u8 kT hlt
    have hb := internal.reflectlite.flag_bits kT hlt (internal.reflectlite.kindOf_pos hkT)
    wp_start as ⟨Hl, Hx⟩
    ihave ⟨%hF, Hx⟩ := internal.reflectlite.valueOfRepr_facts xv T kT y hlt (internal.reflectlite.kindOf_pos hkT) $$ Hx
    have hf : xv.typ_' = go.tok T ∧ (xv.flag' = W64 kT ∨ xv.flag' = W64 kT ||| W64 128) := ⟨hF.1, hF.2.2.2.2⟩
    have hxf : xv.flag' ≠ W64 0 ∧ xv.flag' &&& W64 96 = W64 0 := ⟨hF.2.1, hF.2.2.2.1⟩
    try wp_auto
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hku, hk20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hku, hk20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hku, hk20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 2 (try wp_meth1)
    wp_apply wp_assignTo.1 kT xv _ _ hkT h20 hid hf.1 hf.2 as %fl %hfl
    icases Hx with (⟨%hd, %hxv⟩ | ⟨%q, ⟨%hd, %hxv⟩, Hq⟩)
    · subst hxv
      have : fl &&& W64 128 = W64 0 := by rw [hfl]; exact hb.2.2.2.2.1
      try simp only [this]
      try wp_auto
      wp_apply wp_Store.1 l w y hi $$ [$Hl] as Hl
      iapply HΦ
      iexact Hl
    · subst hxv
      have : fl &&& W64 128 = W64 128 := by rw [hfl]; exact hb.2.2.2.2.2.1
      try simp only [this]
      try wp_auto
      wp_apply wp_Load.1 q (DFrac.own 1) y hi hn $$ [$Hq] as Hq
      wp_apply wp_Store.1 l w y hi $$ [$Hl] as Hl
      iapply HΦ
      iexact Hl
  · intro V _ _ T elems _ _ W _ _ t ut _ _ kt l w y x xv hkt hi hn hts hy
    have hlt := internal.reflectlite.kindOf_lt hkt
    have h20 := internal.reflectlite.kindOf_ne_20 hkt hi
    have hb := internal.reflectlite.flag_bits 20 (by omega) (by omega)
    simp only [show ((20 : Nat) : Int) = 20 from rfl] at hb
    wp_start as ⟨Hl, Hx⟩
    ihave ⟨%hF, Hx⟩ := internal.reflectlite.valueOfRepr_facts xv t kt x hlt (internal.reflectlite.kindOf_pos hkt) $$ Hx
    have hxf : xv.flag' ≠ W64 0 ∧ xv.flag' &&& W64 96 = W64 0 := ⟨hF.2.1, hF.2.2.2.1⟩
    try wp_auto
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, internal.reflectlite.u8_lit20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, internal.reflectlite.u8_lit20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 3 (try wp_meth1)
    iterate 2 (try simp only [hxf.1, hxf.2, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, internal.reflectlite.u8_lit20, decide_true, decide_false, Bool.not_true, Bool.not_false]; try wp_auto)
    iterate 2 (try wp_meth1)
    wp_apply wp_assignTo.2 kt xv _ l w y x hkt hi hn hts hy $$ [$Hl $Hx] as %fl ⟨%hfl, Hl, Hx⟩
    try simp only [hfl]
    try wp_auto
    wp_apply wp_Load.2 l (DFrac.own 1) y (interface.mkOk t #x) hy $$ [$Hl] as Hl
    wp_apply wp_Store.2 (V := V) (T := T) l y y ⟨t, #x⟩ hts hy $$ [$Hl] as Hl
    iapply HΦ
    iexact Hl

end proof

end Perennial
