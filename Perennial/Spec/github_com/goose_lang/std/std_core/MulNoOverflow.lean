/-
`github.com/goose-lang/std/std_core.MulNoOverflow`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

/-- `MulNoOverflow(x, y)`: whether `x * y` does not overflow. -/
abbrev github_com.goose_lang.std.std_core.MulNoOverflow.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x * y) = uint.Z x * uint.Z y)); True }}

end spec

end Perennial
