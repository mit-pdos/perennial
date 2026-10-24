/-
The proof of `strconv.rangeError`.
-/
module

public import Perennial.Spec.strconv.rangeError
public import Perennial.Spec.internal.stringslite.Clone

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

theorem strconv.rangeError.wp_proof
    (wp_Clone : internal.stringslite.Clone.spec (GF := GF) (hG := hG)) :
    strconv.rangeError.spec (GF := GF) (hG := hG) := by
  intro fn str
  wp_start
  ihave Hi := strconv.isInit_access $$ Hpkg
  icases Hi with ⟨#HErrRange, #HErrSyntax⟩
  iunfold errors.newVar at HErrRange
  icases HErrRange with ⟨%x, #Hx, -⟩
  wp_auto
  wp_apply wp_Clone
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iunfold strconv.numErrorOf
  iexists l, _
  iframe Hl Hx
  ipureintro; rfl

end proof

end Perennial
