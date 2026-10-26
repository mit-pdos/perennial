/-
`github.com/goose-lang/std.newJoinHandle`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `newJoinHandle()`: a new `JoinHandle`, for any resource `P`. -/
abbrev github_com.goose_lang.std.newJoinHandle.spec : Prop :=
  ∀ (P : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (Val (@! newJoinHandle)) (Val #()))
    {{ (l : Loc), RET #l; isJoinHandle l P }}

end spec

end Perennial
