/-
The proof of `internal.reflectlite.implements`.
-/
module

public import Perennial.Spec.internal.reflectlite.implements
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.Alloc
public import Perennial.Spec.internal.reflectcore.Load
public import Perennial.Spec.internal.reflectcore.AssertOk

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

theorem internal.reflectlite.implements.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_Alloc : internal.reflectcore.Alloc.spec (GF := GF) (hG := hG))
    (wp_Load : internal.reflectcore.Load.spec (GF := GF) (hG := hG))
    (wp_AssertOk : internal.reflectcore.AssertOk.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.implements.spec (GF := GF) (hG := hG) := by
  constructor
  · intro T uT _ _ kT v hkT h20
    wp_start as #Hinit
    wp_auto
    unfold go.tok
    wp_apply wp_TypeKind kT null hkT
    try rw [internal.reflectlite.kind_w8 hkT]
    simp only [decide_eq_false (internal.reflectlite.kne_20 kT (internal.reflectlite.kindOf_lt hkT) h20)]
    try wp_auto
    iapply HΦ
    itrivial
  · intro T elems _ _ W _ _ V uV _ _ _ kV hkV hi hn
    wp_start as #Hinit
    wp_auto
    unfold go.tok
    wp_apply wp_TypeKind 20 null internal.reflectlite.kindOf_interface
    try rw [internal.reflectlite.kind_w8n 20 (by omega)]
    try wp_auto
    wp_apply wp_TypeKind kV null hkV
    try rw [internal.reflectlite.kind_w8 hkV]
    simp only [decide_eq_false (internal.reflectlite.kne_20 kV (internal.reflectlite.kindOf_lt hkV)
        (internal.reflectlite.kindOf_ne_20 hkV hi))]
    try wp_auto
    wp_apply wp_Alloc (V := W) (T := V) #null as %q Hq
    wp_apply wp_Load.1 q (DFrac.own 1) (zero_val W) hi hn $$ [$Hq] as Hq
    wp_apply wp_AssertOk (T := T) null (interface.mkOk V #(zero_val W))
    iapply HΦ
    itrivial

end proof

end Perennial
