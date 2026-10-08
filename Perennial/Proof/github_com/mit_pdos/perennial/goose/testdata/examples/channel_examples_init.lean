/-
Package initialization instances for the `channel` examples package.
The `IsPkgInit` instance of `channel/lock` comes from the import of `lock.lean`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.strings
public import Perennial.Proof.time
public import Perennial.Proof.sync
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.lock
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  build_get_is_pkg_init_wf

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
