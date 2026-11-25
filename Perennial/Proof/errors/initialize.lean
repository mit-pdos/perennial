/-
The proof of `errors.initialize'`. `ErrUnsupported` is kept with its `errors.New` error's exact type
and field (`errors.wp_New_errorString`, from `New`'s code), as `io`'s variables are; `errorType` is
`reflectlite.TypeOf((*error)(nil)).Elem()`, over the model of `internal/reflectlite`.
-/
module

public import Perennial.Spec.errors.initialize
public import Perennial.Proof.errors.NewVar
public import Perennial.Spec.internal.reflectlite.initialize
public import Perennial.Spec.internal.reflectlite.TypeOf
public import Perennial.Spec.internal.reflectlite.rtype__Elem

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

theorem errors.initialize'.wp_proof
    (wp_reflectlite_initialize : internal.reflectlite.initialize'.spec (GF := GF) (hG := hG))
    (wp_TypeOf : internal.reflectlite.TypeOf.spec (GF := GF) (hG := hG))
    (wp_rtype_Elem : internal.reflectlite.rtype.Elem.spec (GF := GF) (hG := hG)) :
    errors.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) errorType internal.reflectlite.Type'.ty as HET
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupported go.error as HEU
  wp_apply wp_reflectlite_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hrl⟩
  -- the store into `errorType` ends the initializer: keep an update to make the cells
  -- persistent afterwards
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %x #E
  wp_apply wp_TypeOf.1 (go.PointerType go.error) _
  unfold go.tok
  wp_apply wp_rtype_Elem go.error null (by simp [go.typeQuery, go.is_underlying, go.NotLayoutModelled.not_layout_modelled])
  ipersist HEU
  ipersist HET
  ihave #N : errors.newVar (GF := GF) ErrUnsupported _ $$ []
  · iunfold errors.newVar
    iexists _
    iframe HEU E
  imodintro
  iframe Hown
  is_pkg_init_finish
  isplitr
  · itrivial
  imodintro
  imodintro
  unfold errors.isInit
  isplitr
  · iexact N
  · iexact HET

end proof

end Perennial
