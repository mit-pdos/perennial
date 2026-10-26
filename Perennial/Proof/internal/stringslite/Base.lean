/-
Shared definitions of the proofs of `internal/stringslite`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.stringslite

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.stringslite

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.stringslite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.stringslite :=
  build_get_is_pkg_init_wf

end wps

end internal.stringslite

end Perennial
