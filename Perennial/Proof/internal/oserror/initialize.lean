/-
The proof of `internal.oserror.initialize'`. The variables made by `errors.New` are kept with their
exact type (`errors.wp_New_errorString`, from `New`'s code), as `io`'s.
-/
module

public import Perennial.Spec.internal.oserror.initialize
public import Perennial.Spec.errors.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.oserror.Assumptions]

open internal.oserror in
theorem internal.oserror.initialize'.wp_proof
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG)) :
    internal.oserror.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrClosed go.error as HCl
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotExist go.error as HNE
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrExist go.error as HEx
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPermission go.error as HPe
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalid go.error as HIn
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply errors.wp_New_errorString as %xIn #EIn
  ipersist HIn
  wp_apply errors.wp_New_errorString as %xPe #EPe
  ipersist HPe
  wp_apply errors.wp_New_errorString as %xEx #EEx
  ipersist HEx
  wp_apply errors.wp_New_errorString as %xNE #ENE
  ipersist HNE
  -- the store into `ErrClosed` ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xCl #ECl
  ipersist HCl
  ihave #NIn : errors.newVar (GF := GF) ErrInvalid _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HIn EIn
  ihave #NPe : errors.newVar (GF := GF) ErrPermission _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HPe EPe
  ihave #NEx : errors.newVar (GF := GF) ErrExist _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HEx EEx
  ihave #NNE : errors.newVar (GF := GF) ErrNotExist _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HNE ENE
  ihave #NCl : errors.newVar (GF := GF) ErrClosed _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HCl ECl
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe NIn NPe NEx NNE NCl

end proof

end Perennial
