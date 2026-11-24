/-
Shared definitions of the proofs of `github.com/mit-pdos/gokv/grove_ffi`: its `isPkgInit`,
`isListener` and `isConnection` (a `Listener` or `Connection` is a cell holding the Grove
extension's socket value, `Perennial/TrustedCode/github_com/mit_pdos/gokv/grove_ffi.lean`).
-/
module

public import Perennial.Proof.GrovePrelude
public import Perennial.Code.github_com.mit_pdos.gokv.grove_ffi
public import Perennial.GeneratedProof.github_com.mit_pdos.gokv.grove_ffi
public import Perennial.Golang.Theory.String

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.gokv.grove_ffi

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi :=
  build_get_is_pkg_init_wf

/-- `l` is a `Listener` listening on `host`: the package is initialized and `l` holds (for
good) the listen socket of `host`. -/
def isListener (l : Loc) (host : Endpoint) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi ∗
    heapPointsto l DFrac.discard (listen_socket host))

/-- `c` is a `Connection` from `c_l` (local) to `c_r` (remote): the package is initialized and
`c` holds (for good) the connection socket `(c_l, c_r)`. -/
def isConnection (c : Loc) (c_l c_r : Endpoint) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi ∗
    heapPointsto c DFrac.discard (connectionSocket c_l c_r))

instance isListener_persistent (l : Loc) (host : Endpoint) :
    Persistent (isListener (GF := GF) l host) := by
  unfold isListener; infer_instance

instance isConnection_persistent (c : Loc) (c_l c_r : Endpoint) :
    Persistent (isConnection (GF := GF) c c_l c_r) := by
  unfold isConnection; infer_instance

end wps

end github_com.mit_pdos.gokv.grove_ffi

end Perennial
