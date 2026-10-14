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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `errors.New(msg)` as `wp_New`, telling also that the error is a pointer error. (`New`'s one
spec, `errors.wp_New`, under its old name.) -/
theorem errors.wp_New_ptr : errors.New.spec (GF := GF) (hG := hG) :=
  errors.wp_New

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
  wp_apply +noauto wp_Is (· = interface.ok ii) (fun _ => False) (interface.ok ii) target
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
