/-
The proof of `internal.reflectlite.Value.assignTo`.
-/
module

public import Perennial.Spec.internal.reflectlite.Value__assignTo
public import Perennial.Spec.internal.reflectlite.directlyAssignable
public import Perennial.Spec.internal.reflectlite.implements
public import Perennial.Spec.internal.reflectlite.flag__kind
public import Perennial.Spec.internal.reflectlite.Value__Kind
public import Perennial.Spec.internal.reflectlite.valueInterface
public import Perennial.Spec.internal.reflectcore.TypeKind
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

theorem internal.reflectlite.Value.assignTo.wp_proof
    (wp_directlyAssignable : internal.reflectlite.directlyAssignable.spec (GF := GF) (hG := hG))
    (wp_implements : internal.reflectlite.implements.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_Value_Kind : internal.reflectlite.Value.Kind.spec (GF := GF) (hG := hG))
    (wp_valueInterface : internal.reflectlite.valueInterface.spec (GF := GF) (hG := hG))
    (wp_Store : internal.reflectcore.Store.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.Value.assignTo.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  constructor
  · intro T uT _ _ kT xv ctx target hkT h20 hid htyp hf
    wp_start as #Hinit
    try wp_auto
    wp_meths
    rw [htyp]
    wp_apply wp_directlyAssignable kT kT hkT hkT (fun _ => hid) (fun h => absurd rfl h)
    try simp only [decide_true]
    try wp_auto
    wp_meths
    have hb := internal.reflectlite.flag_bits kT (internal.reflectlite.kindOf_lt hkT)
      (internal.reflectlite.kindOf_pos hkT)
    have hro : xv.flag' &&& W64 96 = W64 0 := by
      rcases hf with h | h
      · rw [h]; exact hb.2.2.2.2.2.2.1
      · rw [h]; exact hb.2.2.2.2.2.2.2.1
    try simp only [hro, decide_true, Bool.not_true, Bool.not_false]
    try wp_auto
    try unfold go.tok
    wp_apply wp_TypeKind kT null hkT
    iapply HΦ
    ipureintro
    have hlt := internal.reflectlite.kindOf_lt hkT
    rcases hf with hf | hf
    · rw [hf]; exact (internal.reflectlite.assign_flag_bits kT hlt).1
    · rw [hf]; exact (internal.reflectlite.assign_flag_bits kT hlt).2
  · intro V _ _ T elems _ _ _ W _ _ t ut _ _ _ kt xv ctx l w y x hkt hi hn hts hy
    have hUT : _root_.Perennial.underlying T = go.InterfaceType elems := go.is_underlying
    have hUt : _root_.Perennial.underlying t = ut := go.is_underlying
    have hTt : T ≠ t := by
      intro h; subst h; rw [hUT] at hUt; subst hUt; simp [go.isInterfaceType] at hi
    have h20 := internal.reflectlite.kindOf_ne_20 hkt hi
    have hlt := internal.reflectlite.kindOf_lt hkt
    have hk20 := internal.reflectlite.kne_20 kt hlt h20
    have hku := internal.reflectlite.kind_u8 kt hlt
    wp_start as ⟨Hl, Hx⟩
    ihave ⟨%hF, Hx⟩ := internal.reflectlite.valueOfRepr_facts xv t kt x hlt (internal.reflectlite.kindOf_pos hkt) $$ Hx
    have hf : xv.typ_' = go.tok t ∧ xv.flag' &&& W64 31 = W64 kt := ⟨hF.1, hF.2.2.1⟩
    try wp_auto
    wp_meths
    rw [hf.1]
    wp_apply wp_directlyAssignable (T := T) (V := t) 20 kt internal.reflectlite.kindOf_interface hkt
      (fun h => absurd h hTt) (fun _ => Or.inr (Or.inl (Ne.symm h20)))
    try simp only [hTt, decide_false]
    try wp_auto
    wp_meths
    rw [hf.1]
    wp_apply wp_implements.2 (T := T) (W := W) (V := t) kt hkt hi hn
    rw [hts]
    try wp_auto
    wp_meths
    try wp_apply wp_Value_Kind
    try rw [hf.2, hku]
    try simp only [hk20, decide_false]
    try wp_auto
    wp_apply wp_valueInterface kt xv x hkt hi hn $$ [$Hx] as Hx
    wp_apply wp_Store.2 (V := V) (T := T) l w y ⟨t, #x⟩ hts hy $$ [$Hl] as Hl
    iapply HΦ
    iframe
    ipureintro
    decide

end proof

end Perennial
