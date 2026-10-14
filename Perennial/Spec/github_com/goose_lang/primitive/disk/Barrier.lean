/-
`github.com/goose-lang/primitive/disk.Barrier`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.disk.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE disk_ffi

section spec
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

/-- `Barrier()`: a no-op (there is no crash logic). -/
abbrev github_com.goose_lang.primitive.disk.Barrier.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk }}
      (App (Val (@! Barrier)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
