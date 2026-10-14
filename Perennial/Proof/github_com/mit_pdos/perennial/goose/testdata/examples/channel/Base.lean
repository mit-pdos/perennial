/-
Shared definitions of the proofs of the goose channel examples (package `channel`): the
package's `isPkgInit` instances (the `IsPkgInit` instance of `channel/lock` comes from
the import of its `Base`) and the countability of `Result`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.strings.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Handshake
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel :=
  build_get_is_pkg_init_wf

end proof

instance Result.countable [FfiSyntax] : Pos.Countable Result :=
  .ofInjective (fun r => Pos.Countable.encode (r.value', r.primary_won'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; have h := Pos.encode_inj h; simp_all)

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
