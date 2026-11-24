/-
The proof of `reflect.isDirectIface`.
-/
module

public import Perennial.Spec.reflect.isDirectIface
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Proof.reflect.Values

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

set_option linter.unusedSimpArgs false in
theorem reflect.isDirectIface.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG)) :
    reflect.isDirectIface.spec (GF := GF) (hG := hG) := @fun T u hu k l hk h17 h25 => by
  have hlt := reflect.kindOf_lt hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl h17
    | exact absurd rfl h25
    | (simp only [Nat.reduceEqDiff, or_false, or_true, false_or, true_or, or_self, decide_true,
         decide_false]
       wp_start as #Hinit
       wp_auto
       wp_apply wp_TypeKind _ l hk
       iapply HΦ
       itrivial)

end proof

end Perennial
