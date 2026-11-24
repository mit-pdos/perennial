/-
Shared definitions of the proofs of `internal/bytealg`: its `isPkgInit`, and what
`CompareString` returns.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.bytealg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.bytealg

/-- What `bytealg.CompareString(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`). -/
def compareResult [GooseExts] (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

end wps

end internal.bytealg

end Perennial
