/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_examples_init.v`:
package initialization instances for the `channel` examples package (Rocq
`channel_examples`).

Lean notes:
* The Rocq file also declares the `IsPkgInit` instance of `channel/lock` (a
  duplicate of the one in `lock.v`); here it comes from the import of `lock.lean`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.strings
import Perennial.Proof.time
import Perennial.Proof.sync
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.lock
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

instance is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  build_get_is_pkg_init_wf

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
