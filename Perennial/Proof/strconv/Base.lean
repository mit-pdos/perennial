/-
Shared definitions of the proofs of the Go `strconv` package: its `isPkgInit` (the `errors.New`
errors `ErrRange` and `ErrSyntax`).
-/
module

public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.internal.strconv.Base
public import Perennial.Proof.internal.stringslite.Base
public import Perennial.Code.strconv
public import Perennial.GeneratedProof.strconv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strconv

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- The package-initialized state (persistent; Go never writes these variables after
initialization): each error variable made by `errors.New` holds that error (`errors.newVar`). -/
abbrev isInit : IProp GF :=
  iprop("#HErrRange" ∷ errors.newVar ErrRange go!"value out of range" ∗
  "#HErrSyntax" ∷ errors.newVar ErrSyntax go!"invalid syntax")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.strconv :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strconv :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.strconv ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.strconv

/-- **`err` is a fresh `*NumError` for the function `fn` and the input `s`**, whose `Err` is the
error the package variable `X` holds (`ErrSyntax` or `ErrRange`): what `ParseUint` and the other
parsers return on a failed conversion. -/
def numErrorOf (err : GoInterface) (fn s X : GoString) : IProp GF :=
  iprop(∃ (l : Loc) (e : GoInterface),
    ⌜err = interface.mkOk (go.GoType.PointerType NumError.ty) #l⌝ ∗
    l ↦ NumError.mk fn s e ∗ globalAddr X ↦□ e)

end wps

end strconv

end Perennial
