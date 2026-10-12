/-
`parallel_search_replace.worker`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.worker.spec : Prop :=
  ∀ (γs : ChanNames) (ch : Loc) (wg : Loc) (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "#Hchan" ∷ isChanBag γs ch (chanP wg x y) }}
      (App (App (App (App (Val (@! worker)) (Val #ch)) (Val #wg)) (Val #x)) (Val #y))
    {{ RET #(); True }}

end spec

end Perennial
