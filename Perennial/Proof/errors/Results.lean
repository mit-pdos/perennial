/-
Results of `errors` derived from the linked ones: `wp_New_ptr` (the old name of `New`'s
spec, which tells that the error is a pointer error) and `wp_Is_leaf` (`Is` on a leaf error).
-/
module

public import Perennial.Proof.errors.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `errors.New(msg)` as `wp_New`, telling also that the error is a pointer error. (`New`'s one
spec, `errors.wp_New`, under its old name.) -/
theorem errors.wp_New_ptr : errors.New.spec (GF := GF) (hG := hG) :=
  errors.wp_New

/-- `errors.Is(err, target)` over an over-approximating tree (`errorIsTree S M target`): it returns
`err == target` if either is `nil`; otherwise `true` if `err == target`, and `true` only if some
error of the tree is `target` or has an `Is` method that returned `true` (`M`). -/
theorem errors.wp_Is_tree (S : GoError → Prop) (M : GoInterfaceOk → Prop) (err target : GoError)
    (htarget : ∀ tii, target = interface.ok tii → IsPointerError tii)
    (htyped : TreeTyped S target) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ }}
      (App (App (Val (@! Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b;
        ⌜(err = interface.nil ∨ target = interface.nil) → b = decide (err = target)⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err = target → b = true⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err ≠ interface.nil →
          b = true → ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii)⌝ }} := by
  iintro %Φ ⟨#Hinit, #Htree, %HS⟩ HΦ
  wp_apply +noauto wp_Is S (isRelOf M) (unwrapRelOf S) err target htarget htyped
    $$ [$Hinit $Htree] as %b ⟨%Hnil, %Hw⟩
  · ipureintro; exact HS
  iapply HΦ
  ipureintro
  refine ⟨Hnil, fun tii ht _ heq => ?_, fun tii ht _ hn hb => ?_⟩
  · subst ht
    obtain ⟨ii, rfl⟩ : ∃ ii, err = interface.ok ii := ⟨tii, heq⟩
    exact isWalk_eq_true rfl heq (Hw (by simp) (by simp))
  · subst hb ht
    exact isWalkL_true_mem (Hw hn (by simp)) (fun e he => by rw [List.mem_singleton.mp he]; exact HS)

/-- `errors.Is(err, target)` for a leaf `err` without an `Is` method and a `nil` or pointer
`target` (an `errors.New` error): `err == target`. If `err` has `target`'s type, it holds a
pointer (`TreeTyped`; `treeTyped_pointer` for a pointer error `err`). -/
theorem errors.wp_Is_leaf (ii : GoInterfaceOk) (target : GoError) (hleaf : isLeafError ii)
    (hIs : methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    (htarget : ∀ tii, target = interface.ok tii → IsPointerError tii)
    (htyped : TreeTyped (· = interface.ok ii) target) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
      (App (App (Val (@! Is)) (Val #(interface.ok ii))) (Val #target))
    {{ RET #(decide (interface.ok ii = target)); True }} := by
  iintro %Φ #Hinit HΦ
  ihave #Htree := errorIsTree_leaf (GF := GF) ii (fun _ => False) target hleaf hIs
  wp_apply +noauto errors.wp_Is_tree (· = interface.ok ii) (fun _ => False) (interface.ok ii) target
    htarget htyped $$ [$Hinit $Htree] as %b ⟨%Hnil, %Heq, %Hsome⟩
  · ipureintro; rfl
  have hb : b = decide (interface.ok ii = target) := by
    cases target with
    | nil => exact Hnil (Or.inr rfl)
    | ok tii =>
      have hp := htarget tii rfl
      by_cases h : interface.ok ii = interface.ok tii
      · rw [decide_eq_true h]; exact Heq tii rfl hp h
      · rw [decide_eq_false h]
        cases b
        · rfl
        · obtain ⟨ii', hii', hm⟩ := Hsome tii rfl hp (by simp) rfl
          rw [hii'] at hm
          exact absurd (hm.resolve_right id) h
  rw [← hb]
  iapply HΦ
  itrivial

end results

end Perennial
