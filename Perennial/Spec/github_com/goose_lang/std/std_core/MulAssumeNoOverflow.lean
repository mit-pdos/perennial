/-
`github.com/goose-lang/std/std_core.MulAssumeNoOverflow`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.std_core.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

/-- `MulAssumeNoOverflow(x, y)`: `x * y`, assuming it does not overflow. -/
abbrev github_com.goose_lang.std.std_core.MulAssumeNoOverflow.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x * y); ⌜uint.Z (x * y) = uint.Z x * uint.Z y⌝ }}

end spec

end Perennial
