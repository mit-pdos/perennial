/-
The proof of `strconv.initialize'`. The variables made by `errors.New` are kept with their exact
type (`errors.wp_New_errorString`).
-/
module

public import Perennial.Spec.strconv.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.internal.strconv.initialize
public import Perennial.Spec.internal.stringslite.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem strconv.initialize'.wp_proof
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_strconv_initialize : internal.strconv.initialize'.spec (GF := GF) (hG := hG))
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG)) :
    strconv.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSyntax go.error as HS
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRange go.error as HR
  wp_apply wp_stringslite_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsl⟩
  wp_apply wp_strconv_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hisc⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  -- the printable-rune tables: their trusted initializers do nothing
  repeat wp_call
  wp_apply errors.wp_New_errorString as %xR #ER
  ipersist HR
  -- the store into `ErrSyntax` ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xS #ES
  ipersist HS
  ihave #NR : errors.newVar (GF := GF) ErrRange _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HR ER
  ihave #NS : errors.newVar (GF := GF) ErrSyntax _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HS ES
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe NR NS

end proof

end Perennial
