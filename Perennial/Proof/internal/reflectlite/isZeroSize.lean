/-
The proof of `internal.reflectlite.isZeroSize`.
-/
module

public import Perennial.Spec.internal.reflectlite.isZeroSize
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeLen
public import Perennial.Spec.internal.reflectcore.TypeElem
public import Perennial.Spec.internal.reflectcore.TypeNumField
public import Perennial.Spec.internal.reflectcore.TypeFieldType

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open reflect (directIfaceN zeroSizeN allTrue directKind)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.isZeroSize.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeLen : internal.reflectcore.TypeLen.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG))
    (wp_TypeNumField : internal.reflectcore.TypeNumField.spec (GF := GF) (hG := hG))
    (wp_TypeFieldType : internal.reflectcore.TypeFieldType.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.isZeroSize.spec (GF := GF) (hG := hG) := by
  intro n
  induction n with
  | zero => intro T l b h; simp [reflect.zeroSizeN] at h
  | succ n IH =>
    intro T l b h
    simp only [reflect.zeroSizeN] at h
    split at h
    · rename_i len e hu
      haveI : T ↓u go.ArrayType len e := ⟨hu⟩
      wp_start as #Hinit
      wp_auto
      wp_apply wp_TypeKind 17 l (by simp [go.kindOf])
      try rw [internal.reflectlite.kind_w8n 17 (by omega)]
      try wp_auto
      obtain ⟨hb, h⟩ : (0 ≤ len ∧ len < 2 ^ 63) ∧ (if len = 0 then some true else zeroSizeN n e) = some b := by
        split at h
        · exact ⟨by assumption, h⟩
        · cases h
      wp_apply wp_TypeLen T l #(W64 len) (by simp [go.typeQuery, hu])
      by_cases h0 : len = 0
      · subst h0
        simp only [ite_true, Option.some.injEq] at h
        subst h
        rw [decide_eq_true rfl]
        wp_auto
        iapply HΦ
        itrivial
      · simp only [h0, ite_false] at h
        have hne : W64 len ≠ W64 0 := by word
        rw [decide_eq_false hne]
        wp_auto
        wp_apply wp_TypeElem T l #(go.tok e) (by simp [go.typeQuery, hu])
        unfold go.tok
        wp_apply IH e null b h
        iapply HΦ
        itrivial
      done
      done
    · rename_i fs hu
      haveI : T ↓u go.StructType fs := ⟨hu⟩
      obtain ⟨hb, h⟩ : fs.length < 2 ^ 63 ∧
          allTrue (fs.map fun f => zeroSizeN n (go.fieldDeclType f)) = some b := by
        split at h
        · exact ⟨by assumption, h⟩
        · cases h
      wp_start as #Hinit
      wp_auto
      wp_apply wp_TypeKind 25 l (by simp [go.kindOf])
      try rw [internal.reflectlite.kind_w8n 25 (by omega)]
      try wp_auto
      ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ fs.length ∧
            allTrue ((fs.map fun f => zeroSizeN n (go.fieldDeclType f)).drop (sint.nat i)) =
              some b⌝ : IProp GF) $$ [i]
      · iexists W64 0
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        exact h
      wp_for HI
      wp_apply wp_TypeNumField T l #(W64 fs.length) (by simp [go.typeQuery, hu])
      have hlenZ : sint.Z (W64 (fs.length : Int)) = fs.length := by word
      wp_if_destruct
      · have hlt : sint.Z i < fs.length := by
          have : sint.Z i < sint.Z (W64 (fs.length : Int)) := of_decide_eq_true (go.intoVal_inj Hif)
          omega
        list_elem fs (sint.nat i) as f
        wp_apply wp_TypeFieldType T l i #(go.tok (go.fieldDeclType f))
          (by simp [go.typeQuery, hu, go.listAt, Hi.1, Hf_lookup])
        unfold go.tok
        have hdrop : (fs.map fun f => zeroSizeN n (go.fieldDeclType f)).drop (sint.nat i) =
            zeroSizeN n (go.fieldDeclType f) ::
              (fs.map fun f => zeroSizeN n (go.fieldDeclType f)).drop (sint.nat i + 1) := by
          rw [List.drop_eq_getElem_cons (by simp; word)]
          obtain ⟨_, hf⟩ := List.getElem?_eq_some_iff.mp Hf_lookup
          simp [hf]
        have hall := Hi.2.2
        rw [hdrop] at hall
        cases hz : zeroSizeN n (go.fieldDeclType f) with
        | none => rw [hz] at hall; cases hall
        | some z =>
          rw [hz] at hall
          cases z
          · simp only [allTrue, Option.some.injEq] at hall
            subst hall
            wp_apply IH _ null false hz
            wp_for_post
            iapply HΦ
            itrivial
          · simp only [allTrue] at hall
            wp_apply IH _ null true hz
            wp_for_post
            iframe
            iexists i + W64 1
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
            exact hall
      · have hnlt : ¬ sint.Z i < sint.Z (W64 (fs.length : Int)) :=
          fun hp => Hif (by rw [decide_eq_true hp])
        have hge : sint.Z i = fs.length := by omega
        have hall := Hi.2.2
        rw [show sint.nat i = fs.length by word] at hall
        rw [List.drop_eq_nil_of_le (by simp)] at hall
        simp only [allTrue, Option.some.injEq] at hall
        subst hall
        simp only [decide_eq_false hnlt, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iapply HΦ
        itrivial
    · rename_i ha hs
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h17, h25⟩ := reflect.kindOf_ne_17_25 hk ha hs
      haveI : T ↓u underlying T := ⟨rfl⟩
      have hlt := internal.reflectlite.kindOf_lt hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact absurd rfl h17
        | exact absurd rfl h25
        | (wp_start as #Hinit
           wp_auto
           wp_apply wp_TypeKind _ l hk
           try rw [internal.reflectlite.kind_w8 hk]
           try wp_auto
           iapply HΦ
           itrivial)

end proof

end Perennial
