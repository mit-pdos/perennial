/-
The proof of `io.initialize'`. The variables made by `errors.New` are kept with their exact
type (`errors.wp_New_errorString`, from `New`'s code: `errors.New.spec` keeps it abstract).
-/
module

public import Perennial.Spec.io.initialize
public import Perennial.Spec.sync.initialize
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
variable [package_sem : io.Assumptions]

theorem io.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG)) :
    io.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrClosedPipe go.error as HCP
  wp_apply wp_GlobalAlloc (V := sync.Pool) blackHolePool sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoInterface) Discard Writer.ty as HD
  wp_apply wp_GlobalAlloc (V := GoInterface) errOffset go.error as HOff
  wp_apply wp_GlobalAlloc (V := GoInterface) errWhence go.error as HWh
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNoProgress go.error as HNP
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnexpectedEOF go.error as HUE
  wp_apply wp_GlobalAlloc (V := GoInterface) EOF go.error as HEOF
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrShortBuffer go.error as HSB
  wp_apply wp_GlobalAlloc (V := GoInterface) errInvalidWrite go.error as HIW
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrShortWrite go.error as HSW
  wp_apply wp_sync_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply errors.wp_New_errorString as %xSW #ESW
  ipersist HSW
  wp_apply errors.wp_New_errorString as %xIW #EIW
  ipersist HIW
  wp_apply errors.wp_New_errorString as %xSB #ESB
  ipersist HSB
  wp_apply errors.wp_New_errorString as %xEOF #EEOF
  ipersist HEOF
  wp_apply errors.wp_New_errorString as %xUE #EUE
  ipersist HUE
  wp_apply errors.wp_New_errorString as %xNP #ENP
  ipersist HNP
  wp_apply errors.wp_New_errorString as %xWh #EWh
  ipersist HWh
  wp_apply errors.wp_New_errorString as %xOff #EOff
  ipersist HOff
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  ipersist HD
  -- the store into `ErrClosedPipe` ends the initializer: keep an update to make its cell
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xCP #ECP
  ipersist HCP
  ihave #NSW : errors.newVar (GF := GF) ErrShortWrite _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HSW ESW
  ihave #NIW : errors.newVar (GF := GF) errInvalidWrite _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HIW EIW
  ihave #NSB : errors.newVar (GF := GF) ErrShortBuffer _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HSB ESB
  ihave #NEOF : errors.newVar (GF := GF) EOF _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HEOF EEOF
  ihave #NUE : errors.newVar (GF := GF) ErrUnexpectedEOF _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HUE EUE
  ihave #NNP : errors.newVar (GF := GF) ErrNoProgress _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HNP ENP
  ihave #NWh : errors.newVar (GF := GF) errWhence _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HWh EWh
  ihave #NOff : errors.newVar (GF := GF) errOffset _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HOff EOff
  ihave #NCP : errors.newVar (GF := GF) ErrClosedPipe _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HCP ECP
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iunfold isInit
  iframe NSW NIW NSB NEOF NUE NNP NWh NOff NCP
  iexists _
  iexact HD

end proof

end Perennial
