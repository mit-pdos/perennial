/-
`github.com/goose-lang/std.(*JoinHandle).Join`'s spec.
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

/-- `h.Join()`: waits for the goroutine of `h` and gets its resource `P`. -/
abbrev github_com.goose_lang.std.JoinHandle.Join.spec : Prop :=
  ∀ (l : Loc) (P : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ isJoinHandle l P }}
      (App (Val (l @!! go.GoType.PointerType JoinHandle.ty @!! go!"Join")) (Val #()))
    {{ RET #(); P }}

end spec

end Perennial
