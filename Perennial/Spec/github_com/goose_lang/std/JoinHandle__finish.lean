/-
`github.com/goose-lang/std.(*JoinHandle).finish`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `h.finish()`: hands `P` to the joiner of `h`. -/
abbrev github_com.goose_lang.std.JoinHandle.finish.spec : Prop :=
  ∀ (l : Loc) (P : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ isJoinHandle l P ∗ P }}
      (App (Val (l @!! go.GoType.PointerType JoinHandle.ty @!! go!"finish")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
