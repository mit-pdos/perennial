/-
The proof of `internal.reflectlite.isDirectIface`.
-/
module

public import Perennial.Spec.internal.reflectlite.isDirectIface
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

theorem internal.reflectlite.isDirectIface.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeLen : internal.reflectcore.TypeLen.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG))
    (wp_TypeNumField : internal.reflectcore.TypeNumField.spec (GF := GF) (hG := hG))
    (wp_TypeFieldType : internal.reflectcore.TypeFieldType.spec (GF := GF) (hG := hG))
    (wp_isZeroSize : internal.reflectlite.isZeroSize.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.isDirectIface.spec (GF := GF) (hG := hG) := by
  intro n
  induction n with
  | zero => intro T l b h; simp [reflect.directIfaceN] at h
  | succ n IH =>
    intro T l b h
    have hm : go.layoutModelled T = false := reflect.notLayoutModelled_of_directIfaceN h
    haveI : go.NotLayoutModelled T := ⟨hm⟩
    simp only [reflect.directIfaceN, hm, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i len e hu
      haveI : T ↓u go.ArrayType len e := ⟨hu⟩
      obtain ⟨hb, h⟩ : (0 ≤ len ∧ len < 2 ^ 63) ∧
          (if len = 1 then directIfaceN n e else some false) = some b := by
        split at h
        · exact ⟨by assumption, h⟩
        · cases h
      wp_start as #Hinit
      wp_auto
      wp_apply wp_TypeKind 17 l (by simp [go.kindOf])
      try rw [internal.reflectlite.kind_w8n 17 (by omega)]
      try wp_auto
      wp_apply wp_TypeLen T l #(W64 len) (by simp [go.typeQuery, hm, hu])
      by_cases h1 : len = 1
      · subst h1
        simp only [ite_true] at h
        rw [decide_eq_true rfl]
        wp_auto
        wp_apply wp_TypeElem T l #(go.tok e) (by simp [go.typeQuery, hm, hu])
        unfold go.tok
        wp_apply IH e null b h
        iapply HΦ
        itrivial
      · simp only [h1, ite_false, Option.some.injEq] at h
        subst h
        have hne : W64 len ≠ W64 1 := by word
        rw [decide_eq_false hne]
        wp_auto
        iapply HΦ
        itrivial
    · rename_i fs hu
      haveI : T ↓u go.StructType fs := ⟨hu⟩
      obtain ⟨hb, h⟩ : fs.length < 2 ^ 63 ∧ (match fs.getLast? with
          | none => some false
          | some f =>
            match directIfaceN n (go.fieldDeclType f) with
            | some true => allTrue (List.map (fun f => zeroSizeN n (go.fieldDeclType f)) fs.dropLast)
            | some false => some false
            | none => none) = some b := by
        split at h
        · exact ⟨by assumption, h⟩
        · cases h
      have hlenZ : sint.Z (W64 (fs.length : Int)) = fs.length := by word
      wp_start as #Hinit
      wp_auto
      wp_apply wp_TypeKind 25 l (by simp [go.kindOf])
      try rw [internal.reflectlite.kind_w8n 25 (by omega)]
      try wp_auto
      wp_apply wp_TypeNumField T l #(W64 fs.length) (by simp [go.typeQuery, hm, hu])
      cases hlast : fs.getLast? with
      | none =>
        simp only [hlast, Option.some.injEq] at h
        subst h
        have : fs = [] := List.getLast?_eq_none_iff.mp hlast
        subst this
        have h0 : decide (W64 ((([] : List go.field_decl).length : Int)) = W64 0) = true := by
          simp
        rw [h0]
        wp_auto
        iapply HΦ
        itrivial
      | some f =>
        simp only [hlast] at h
        have hne0 : fs ≠ [] := by intro h0; subst h0; simp at hlast
        have hpos : 0 < fs.length := List.length_pos_iff.mpr hne0
        have hne : W64 (fs.length : Int) ≠ W64 0 := by word
        have hm1 : sint.Z (W64 (fs.length : Int) - W64 1) = fs.length - 1 := by word
        rw [decide_eq_false hne]
        wp_auto
        have hq : go.typeQuery .fieldType T (sint.Z (W64 (fs.length : Int) - W64 1)) =
            some #(go.tok (go.fieldDeclType f)) := by
          rw [List.getLast?_eq_getElem?] at hlast
          simp only [go.typeQuery, hm, hu, hm1, go.listAt, Bool.false_eq_true, false_and, ↓reduceIte]
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show ((fs.length : Int) - 1).toNat = fs.length - 1 by omega, hlast]
          rfl
        wp_apply wp_TypeFieldType T l (W64 (fs.length : Int) - W64 1) #(go.tok (go.fieldDeclType f)) hq
        unfold go.tok
        have hdl : (fs.dropLast).length = fs.length - 1 := List.length_dropLast
        cases hd : directIfaceN n (go.fieldDeclType f) with
        | none => rw [hd] at h; cases h
        | some d =>
          cases d
          · simp only [hd, Option.some.injEq] at h
            subst h
            wp_apply IH _ null false hd
            iapply HΦ
            itrivial
          · simp only [hd] at h
            wp_apply IH _ null true hd
            ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
                "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ fs.length - 1 ∧
                  allTrue ((fs.dropLast.map fun f => zeroSizeN n (go.fieldDeclType f)).drop
                    (sint.nat i)) = some b⌝ : IProp GF) $$ [i]
            · iexists W64 0
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
              exact h
            wp_for HI
            wp_if_destruct
            · have hlt : sint.Z i < fs.length - 1 := by
                omega
              list_elem fs.dropLast (sint.nat i) as g
              have hg : fs[sint.nat i]? = some g := by
                rw [List.getElem?_dropLast] at Hg_lookup
                split at Hg_lookup
                · exact Hg_lookup
                · cases Hg_lookup
              wp_apply wp_TypeFieldType T l i #(go.tok (go.fieldDeclType g))
                (by simp [go.typeQuery, hm, hu, go.listAt, Hi.1, hg])
              unfold go.tok
              have hdrop : (fs.dropLast.map fun f => zeroSizeN n (go.fieldDeclType f)).drop
                    (sint.nat i) =
                  zeroSizeN n (go.fieldDeclType g) ::
                    (fs.dropLast.map fun f => zeroSizeN n (go.fieldDeclType f)).drop
                      (sint.nat i + 1) := by
                rw [List.drop_eq_getElem_cons (by simp; word)]
                obtain ⟨_, hf⟩ := List.getElem?_eq_some_iff.mp hg
                simp [hf]
              have hall := Hi.2.2
              rw [hdrop] at hall
              cases hz : zeroSizeN n (go.fieldDeclType g) with
              | none => rw [hz] at hall; cases hall
              | some z =>
                rw [hz] at hall
                cases z
                · simp only [allTrue, Option.some.injEq] at hall
                  subst hall
                  wp_apply wp_isZeroSize n _ null false hz
                  wp_for_post
                  iapply HΦ
                  itrivial
                · simp only [allTrue] at hall
                  wp_apply wp_isZeroSize n _ null true hz
                  wp_for_post
                  iframe
                  iexists i + W64 1
                  iframe
                  ipureintro
                  refine ⟨by word, by word, ?_⟩
                  rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
                  exact hall
            · have hge : sint.Z i = fs.length - 1 := by omega
              have hall := Hi.2.2
              rw [show sint.nat i = fs.dropLast.length by word] at hall
              rw [List.drop_eq_nil_of_le (by simp)] at hall
              simp only [allTrue, Option.some.injEq] at hall
              subst hall
              iapply HΦ
              itrivial
    · rename_i ha hs
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h17, h25⟩ := reflect.kindOf_ne_17_25 hk ha hs
      haveI : T ↓u underlying T := ⟨rfl⟩
      have hlt := internal.reflectlite.kindOf_lt hk
      unfold reflect.directKind
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact absurd rfl h17
        | exact absurd rfl h25
        | (simp only [Nat.reduceEqDiff, _root_.or_false, _root_.or_true, _root_.or_self, _root_.decide_true,
             _root_.decide_false]
           wp_start as #Hinit
           wp_auto
           wp_apply wp_TypeKind _ l hk
           try rw [internal.reflectlite.kind_w8 hk]
           try wp_auto
           iapply HΦ
           itrivial)

end proof

end Perennial
