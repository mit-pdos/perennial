/-
Shared definitions of the proofs of the Go `io` package: its `isPkgInit` (the fixed
`Discard` writer).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.errors.Base
public import Perennial.Code.io
public import Perennial.GeneratedProof.io

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace io

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- The package-initialized state: `Discard` holds a fixed `Writer` (Go never writes it
after initialization; `go.etcd.io/raft/v3`'s initializer loads it), a `discard{}`: its
dynamic type is `io.discard` (an empty struct, so comparable: `log.Logger.SetOutput`
compares its writer with `Discard`). -/
abbrev isInit : IProp GF :=
  iprop(∃ v : val, typedPointsto (globalAddr Discard) (interface.mkOk discard.ty v) DFrac.discard)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io

end wps

end io

end Perennial
