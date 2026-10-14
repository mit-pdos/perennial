/-
`github.com/goose-lang/std.SumAssumeNoOverflow`'s spec.
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

/-- `SumAssumeNoOverflow(x, y)`: `x + y`, assuming it does not overflow. -/
abbrev github_com.goose_lang.std.SumAssumeNoOverflow.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (App (Val (@! SumAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x + y); ⌜uint.Z (x + y) = uint.Z x + uint.Z y⌝ }}

end spec

end Perennial
