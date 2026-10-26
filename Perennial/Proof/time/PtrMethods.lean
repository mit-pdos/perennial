/-
The methods of `*Time` that Go lifts from the value methods of `Time` (`ptr_Add_unfold`, ... in
the method set of `*Time`: load `*l`, call the value method): `Add`, `Before` and `Sub` on a
pointer, from the value method's spec. Not Go functions of their own (goose generates the
wrappers); used by the proofs of `Sub`, `Since` and `Until`, and stated for the linked specs in
`Results.lean` (`Time.wp_ptr_Add`, ...).
-/
module

public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.Time__Sub

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace time

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `(*Time).Add`: the value method on `*l` (`ptr_Add_unfold`, the method set of `*Time`). -/
theorem Time.wp_ptr_Add_of (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (l : Loc) (t : time.Time) (d : time.Duration) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t' : time.Time), RET #t'; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_Add as %t' -
  iapply HΦ $$ Hl

/-- `(*Time).Before`. -/
theorem Time.wp_ptr_Before_of (wp_Before : time.Time.Before.spec (GF := GF) (hG := hG))
    (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_Before as %b -
  iapply HΦ $$ Hl

/-- `(*Time).Sub`. -/
theorem Time.wp_ptr_Sub_of (wp_Sub : time.Time.Sub.spec (GF := GF) (hG := hG))
    (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Sub")) (Val #u))
    {{ (d : w64), RET #d; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_Sub as %d -
  iapply HΦ $$ Hl

end wps

end time

end Perennial
