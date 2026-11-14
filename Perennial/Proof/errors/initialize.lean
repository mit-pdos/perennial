/-
The proof of `errors.initialize'`. `ErrUnsupported` is kept with its `errors.New` error's exact type
and field (`errors.wp_New_errorString`, from `New`'s code), as `io`'s variables are.
-/
module

public import Perennial.Spec.errors.initialize
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

theorem errors.initialize'.wp_proof :
    errors.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupported go.error as HEU
  wp_apply errors.wp_New_errorString as %x #E
  ipersist HEU
  ihave #N : errors.newVar (GF := GF) ErrUnsupported _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HEU E
  -- errorType: its trusted initializer does nothing
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
