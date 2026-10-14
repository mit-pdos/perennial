/-
`github.com/goose-lang/std.Assert`'s spec.
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

/-- `Assert(cond)`: returns if `cond` holds (and panics otherwise). -/
abbrev github_com.goose_lang.std.Assert.spec : Prop :=
  ∀ (cond : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ ⌜cond = true⌝ }}
      (App (Val (@! Assert)) (Val #cond))
    {{ RET #(); True }}

end spec

end Perennial
