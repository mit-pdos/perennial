/-
The proof of `internal.reflectlite.isModelRType`.
-/
module

public import Perennial.Spec.internal.reflectlite.isModelRType
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeNumField
public import Perennial.Spec.internal.reflectcore.TypeFieldType

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

theorem internal.reflectlite.isModelRType.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeNumField : internal.reflectcore.TypeNumField.spec (GF := GF) (hG := hG))
    (wp_TypeFieldType : internal.reflectcore.TypeFieldType.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.isModelRType.spec (GF := GF) (hG := hG) := @fun T u _ k l h hlen => by
  have hU : GoSemanticsFunctions.underlying T = u := go.is_underlying
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TypeKind k l h
  rw [internal.reflectlite.kind_w8 h]
  by_cases hs : ∃ fs, u = go.StructType fs
  · obtain ⟨fs, rfl⟩ := hs
    have hk : k = 25 := by simp [go.kindOf] at h; omega
    subst hk
    have hl := hlen fs rfl
    try wp_auto
    wp_apply wp_TypeNumField T l #(W64 (fs.length : Int)) (by simp [go.typeQuery, hU])
    by_cases h1 : fs.length = 1
    · obtain ⟨f, rfl⟩ : ∃ f, fs = [f] := by
        match fs, h1 with
        | [f], _ => exact ⟨f, rfl⟩
      rw [show decide (W64 ((([f] : List go.field_decl).length : Nat) : Int) = W64 1) = true by simp]
      try wp_auto
      wp_apply wp_TypeFieldType T l (W64 0) #(go.tok (go.fieldDeclType f))
        (by simp [go.typeQuery, hU, go.listAt])
      try unfold go.tok
      try wp_auto
      by_cases hf : go.fieldDeclType f = go.any
      · simp only [internal.reflectlite.rtypeLayoutU, hf, decide_true]
        try rw [if_pos rfl]
        try wp_auto
        iapply HΦ
        itrivial
      · have hne : go.PointerType (go.fieldDeclType f) ≠ go.PointerType go.any := by simpa using hf
        simp only [internal.reflectlite.rtypeLayoutU, hf, decide_false]
        try rw [if_neg hne]
        try wp_auto
        iapply HΦ
        itrivial
    · have hne : W64 (fs.length : Int) ≠ W64 1 := by word
      simp only [decide_eq_false hne]
      try wp_auto
      have hr : internal.reflectlite.rtypeLayoutU (go.StructType fs) = false := by
        match fs, h1 with
        | [], _ => rfl
        | _ :: _ :: _, _ => rfl
      rw [hr]
      iapply HΦ
      itrivial
  · have h25 := internal.reflectlite.kindOf_ne_25 h (fun fs he => hs ⟨fs, he⟩)
    simp only [decide_eq_false (internal.reflectlite.kne_25 k (internal.reflectlite.kindOf_lt h) h25)]
    try wp_auto
    have hr : internal.reflectlite.rtypeLayoutU u = false := by
      unfold internal.reflectlite.rtypeLayoutU
      split
      · exact absurd ⟨_, rfl⟩ hs
      · rfl
    rw [hr]
    iapply HΦ
    itrivial

end proof

end Perennial
