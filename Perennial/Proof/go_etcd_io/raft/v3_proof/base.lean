/-
Port of `new/proof/go_etcd_io/raft/v3_proof/base.v`: package initialization
instances for `go.etcd.io/raft/v3` and the packages it imports.

Lean notes:
* Rocq defines `IsPkgInit` instances for `strings`, `math`, `bytes`, `log`,
  `io` and `errors` here; in Lean those instances already exist in
  `Perennial/Proof/{strings,math,bytes,log,io,errors}.lean`, which are imported
  instead of redefined.
* The instances for `os`, `crypto/rand`, `math/big` and `strconv` (all with
  user part `True`) are needed by `define_is_pkg_init` for `raft` and
  `quorum` (Rocq: computed from the imports as well; Rocq's `raftpb`,
  `quorum`, `tracker`, `confchange` instances are ported as is).
-/
import Perennial.Code.go_etcd_io.raft.v3
import Perennial.GeneratedProof.go_etcd_io.raft.v3
import Perennial.GeneratedProof.go_etcd_io.raft.v3.raftpb
import Perennial.Proof.ProofPrelude
import Perennial.Proof.context
import Perennial.Proof.sync
import Perennial.Proof.fmt
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.cmp
import Perennial.Proof.encoding.binary
import Perennial.Proof.strings
import Perennial.Proof.math
import Perennial.Proof.bytes
import Perennial.Proof.log
import Perennial.Proof.io
import Perennial.Proof.errors

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.raft.v3

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

instance raftpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance raftpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf

instance strconv_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.strconv :=
  define_is_pkg_init iprop(True)
instance strconv_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strconv :=
  build_get_is_pkg_init_wf

instance quorum_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  define_is_pkg_init iprop(True)
instance quorum_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  build_get_is_pkg_init_wf

instance tracker_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  define_is_pkg_init iprop(True)
instance tracker_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  build_get_is_pkg_init_wf

instance confchange_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  define_is_pkg_init iprop(True)
instance confchange_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  build_get_is_pkg_init_wf

instance big_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.math.big :=
  define_is_pkg_init iprop(True)
instance big_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.big :=
  build_get_is_pkg_init_wf

instance rand_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.crypto.rand :=
  define_is_pkg_init iprop(True)
instance rand_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.rand :=
  build_get_is_pkg_init_wf

instance os_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(True)
instance os_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

/-- Rocq `isInitialized`. -/
def isInitialized : IProp GF :=
  iprop(∃ errStopped : GoInterface,
    "ErrStopped" ∷ (globalAddr ErrStopped ↦□ errStopped : IProp GF) ∗
    "%HErrStopped" ∷ ⌜errStopped ≠ interface.nil⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init isInitialized
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.raft.v3

end Perennial
