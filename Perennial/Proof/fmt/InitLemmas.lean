/-
Access to `fmt`'s package-initialized state (`isInit`, `Base.lean`) from `isPkgInit pkg_id.fmt`.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `isPkgInit pkg_id.fmt` holds the package's `isInit`. -/
theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.fmt

/-- The pool `ppFree` of `isPkgInit pkg_id.fmt`: a `sync.Pool` of printers (`ppFreeElem`), whose
`New` needs nothing. -/
theorem isPkgInit_ppFree :
    isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢
      ∃ f : GoFunc, ⌜f ≠ func.nil⌝ ∗ sync.isPool (globalAddr ppFree) f iprop(True) ppFreeElem := by
  iintro #H
  ihave Hi := isInit_access $$ H
  unfold isInit
  iexact Hi

end lemmas

end fmt

end Perennial
