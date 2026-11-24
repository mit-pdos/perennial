/-
The proof of `internal.reflectlite.directlyAssignable`.
-/
module

public import Perennial.Spec.internal.reflectlite.directlyAssignable
public import Perennial.Spec.internal.reflectcore.TypeIdentByName
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeUnderlying
public import Perennial.Spec.internal.reflectlite.isDefined

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

theorem internal.reflectlite.directlyAssignable.wp_proof
    (wp_TypeIdentByName : internal.reflectcore.TypeIdentByName.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeUnderlying : internal.reflectcore.TypeUnderlying.spec (GF := GF) (hG := hG))
    (wp_isDefined : internal.reflectlite.isDefined.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.directlyAssignable.spec (GF := GF) (hG := hG) :=
    @fun T V uT uV _ _ kT kV hkT hkV hid hne => by
  have hUT : GoSemanticsFunctions.underlying T = uT := go.is_underlying
  have hUV : GoSemanticsFunctions.underlying V = uV := go.is_underlying
  have hlt := internal.reflectlite.kindOf_lt hkT
  wp_start as #Hinit
  try wp_auto
  by_cases hTV : T = V
  · subst hTV
    try unfold go.tok
    try wp_auto
    wp_apply wp_TypeIdentByName T null
    rw [hid rfl]
    try wp_auto
    simp only [decide_true]
    iapply HΦ
    itrivial
  · have hneq : go.PointerType T ≠ go.PointerType V := by simpa using hTV
    try unfold go.tok
    try wp_auto
    try rw [if_neg hneq]
    try wp_auto
    wp_apply wp_TypeKind kT null hkT
    try rw [internal.reflectlite.kind_w8 hkT]
    try wp_auto
    rw [show (interface.mkOk (go.PointerType T) #null : GoInterface) = go.tok T from rfl]
    wp_apply wp_isDefined (T := T) kT hkT
    cases hdT : internal.reflectlite.isDefinedT T
    · try wp_auto
      try unfold go.tok
      wp_apply wp_TypeKind kV null hkV
      try rw [internal.reflectlite.kind_w8 hkV]
      by_cases hk : kT = kV
      · subst hk
        obtain ⟨huu, h18, h19, h20, h25⟩ : uT ≠ uV ∧ kT ≠ 18 ∧ kT ≠ 19 ∧ kT ≠ 20 ∧ kT ≠ 25 := by
          rcases hne hTV with h | h | h
          · simp [hdT] at h
          · exact absurd rfl h
          · exact h
        try simp only [decide_true, Bool.not_true]
        try wp_auto
        iterate 4 (try simp only [decide_eq_false (internal.reflectlite.kne_25 kT hlt h25), decide_eq_false (internal.reflectlite.kne_20 kT hlt h20), decide_eq_false (internal.reflectlite.kne_19 kT hlt h19), decide_eq_false (internal.reflectlite.kne_18 kT hlt h18), Bool.false_eq_true, ↓reduceIte]; try wp_auto)
        wp_apply wp_TypeUnderlying T null
        wp_apply wp_TypeUnderlying V null
        rw [hUT, hUV]
        try unfold go.tok
        have hneq : go.PointerType uT ≠ go.PointerType uV := by simpa using huu
        try rw [if_neg hneq]
        try wp_auto
        simp only [hTV, decide_false]
        iapply HΦ
        itrivial
      · simp only [decide_eq_false (internal.reflectlite.kind_ne kT kV hlt (internal.reflectlite.kindOf_lt hkV) hk)]
        try wp_auto
        simp only [hTV, decide_false]
        iapply HΦ
        itrivial
    · try wp_auto
      rw [show (interface.mkOk (go.PointerType V) #null : GoInterface) = go.tok V from rfl]
      wp_apply wp_isDefined (T := V) kV hkV
      cases hdV : internal.reflectlite.isDefinedT V
      · try wp_auto
        try unfold go.tok
        wp_apply wp_TypeKind kV null hkV
        try rw [internal.reflectlite.kind_w8 hkV]
        by_cases hk : kT = kV
        · subst hk
          obtain ⟨huu, h18, h19, h20, h25⟩ : uT ≠ uV ∧ kT ≠ 18 ∧ kT ≠ 19 ∧ kT ≠ 20 ∧ kT ≠ 25 := by
            rcases hne hTV with h | h | h
            · simp [hdT, hdV] at h
            · exact absurd rfl h
            · exact h
          try simp only [decide_true, Bool.not_true]
          try wp_auto
          iterate 4 (try simp only [decide_eq_false (internal.reflectlite.kne_25 kT hlt h25), decide_eq_false (internal.reflectlite.kne_20 kT hlt h20), decide_eq_false (internal.reflectlite.kne_19 kT hlt h19), decide_eq_false (internal.reflectlite.kne_18 kT hlt h18), Bool.false_eq_true, ↓reduceIte]; try wp_auto)
          wp_apply wp_TypeUnderlying T null
          wp_apply wp_TypeUnderlying V null
          rw [hUT, hUV]
          try unfold go.tok
          have hneq : go.PointerType uT ≠ go.PointerType uV := by simpa using huu
          try rw [if_neg hneq]
          try wp_auto
          simp only [hTV, decide_false]
          iapply HΦ
          itrivial
        · simp only [decide_eq_false (internal.reflectlite.kind_ne kT kV hlt (internal.reflectlite.kindOf_lt hkV) hk)]
          try wp_auto
          simp only [hTV, decide_false]
          iapply HΦ
          itrivial
      · try wp_auto
        simp only [hTV, decide_false]
        iapply HΦ
        itrivial

end proof

end Perennial
