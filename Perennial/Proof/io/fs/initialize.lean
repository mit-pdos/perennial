/-
The proof of `io.fs.initialize'`: the error variables hold `internal/oserror`'s errors (each
`errX()` returns one), `SkipDir` and `SkipAll` are made by `errors.New` (kept with their exact type,
`errors.wp_New_errorString`, as `io`'s), and the `var _ I = (*subFS)(nil)` assertions convert a
`nil` pointer.
-/
module

public import Perennial.Spec.io.fs.initialize
public import Perennial.Spec.time.initialize
public import Perennial.Spec.internal.oserror.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.io.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.fs.Assumptions]

open io.fs in
theorem io.fs.initialize'.wp_proof
    (wp_time_initialize : time.initialize'.spec (GF := GF) (hG := hG))
    (wp_oserror_initialize : internal.oserror.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG)) :
    io.fs.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) SkipAll go.error as HSA
  wp_apply wp_GlobalAlloc (V := GoInterface) SkipDir go.error as HSD
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrClosed go.error as HCl
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotExist go.error as HNE
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrExist go.error as HEx
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPermission go.error as HPe
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalid go.error as HIn
  wp_apply wp_io_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_errors_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_oserror_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hoserror⟩
  wp_apply wp_time_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Htime⟩
  ihave #Hos := internal.oserror.isInit_access $$ Hoserror
  icases Hos with ⟨#VIn, #VPe, #VEx, #VNE, #VCl⟩
  iunfold errors.newVar at VIn
  icases VIn with ⟨%xIn, #OIn, #EIn⟩
  iunfold errors.newVar at VPe
  icases VPe with ⟨%xPe, #OPe, #EPe⟩
  iunfold errors.newVar at VEx
  icases VEx with ⟨%xEx, #OEx, #EEx⟩
  iunfold errors.newVar at VNE
  icases VNE with ⟨%xNE, #ONE, #ENE⟩
  iunfold errors.newVar at VCl
  icases VCl with ⟨%xCl, #OCl, #ECl⟩
  wp_func_call
  wp_call
  wp_auto
  ipersist HIn
  wp_func_call
  wp_call
  wp_auto
  ipersist HPe
  wp_func_call
  wp_call
  wp_auto
  ipersist HEx
  wp_func_call
  wp_call
  wp_auto
  ipersist HNE
  wp_func_call
  wp_call
  wp_auto
  ipersist HCl
  wp_apply errors.wp_New_errorString as %xSD #ESD
  ipersist HSD
  -- the store into `SkipAll` ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xSA #ESA
  ipersist HSA
  ihave #NIn : errors.newVar (GF := GF) ErrInvalid go!"invalid argument" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HIn EIn
  ihave #NPe : errors.newVar (GF := GF) ErrPermission go!"permission denied" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HPe EPe
  ihave #NEx : errors.newVar (GF := GF) ErrExist go!"file already exists" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HEx EEx
  ihave #NNE : errors.newVar (GF := GF) ErrNotExist go!"file does not exist" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HNE ENE
  ihave #NCl : errors.newVar (GF := GF) ErrClosed go!"file already closed" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HCl ECl
  ihave #NSD : errors.newVar (GF := GF) SkipDir _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HSD ESD
  ihave #NSA : errors.newVar (GF := GF) SkipAll _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HSA ESA
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe NIn NPe NEx NNE NCl NSD NSA

end proof

end Perennial
