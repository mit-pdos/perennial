/-
Port of `new/golang/theory/chan/au_spec/chan_init.v`: package initialization
predicate for the channel model package
(`github.com/mit-pdos/perennial/goose/model/channel`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.github_com.mit_pdos.perennial.goose.model.channel
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.channel
import Perennial.Proof.github_com.goose_lang.primitive

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.perennial.goose.model.channel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.model.channel :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.model.channel :=
  build_get_is_pkg_init_wf

end proof

end github_com.mit_pdos.perennial.goose.model.channel

end Perennial
