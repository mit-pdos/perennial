/-
`sync.NewCond`'s spec.
-/
module

public import Perennial.Proof.sync.CondDefs

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
variable [package_sem : sync.Assumptions]

abbrev sync.NewCond.spec : Prop :=
  ∀ (m : GoInterfaceOk),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! NewCond)) (Val #(interface.ok m)))
    {{ (c : Loc), RET #c; isCond c m }}

end spec

end Perennial
