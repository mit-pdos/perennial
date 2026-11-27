/-
`strconv.NumError.Error`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `e.Error()` (`"strconv." + e.Func + ": parsing " + Quote(e.Num) + ": " + e.Err.Error()`), of
a `*NumError` whose `Err` is a non-nil error whose `Error()` returns: some string; it only reads
`e`. (A nil `Err` panics, as Go's method call on a nil interface does.) -/
abbrev strconv.NumError.Error.spec : Prop :=
  ∀ (l : Loc) (v : strconv.NumError) (dq : DFrac) (ei : GoInterfaceOk),
    v.Err' = interface.ok ei →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ l ↦{dq} v ∗ strconv.errorReturns ei }}
      (App (Val (l @!! go.GoType.PointerType strconv.NumError.ty @!! go!"Error")) (Val #()))
    {{ (str : GoString), RET #str; l ↦{dq} v }}

end spec

end Perennial
