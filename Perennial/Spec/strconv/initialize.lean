/-
`strconv.initialize'`'s spec.
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

/-- The package's `initialize'`: initialize `internal/stringslite`, `internal/strconv` and
`errors`, allocate and set the package's variables (the printable-rune tables, the two `error`s
made with `errors.New`). -/
abbrev strconv.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.strconv get_is_pkg_init),
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.strconv }}

end spec

end Perennial
