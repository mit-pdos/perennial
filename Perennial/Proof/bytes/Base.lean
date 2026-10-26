/-
Shared definitions of the proofs of the Go `bytes` package: its `isPkgInit` and
`compareResult`, what `bytes.Compare` returns.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Code.bytes
public import Perennial.GeneratedProof.bytes

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bytes

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.bytes :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.bytes :=
  build_get_is_pkg_init_wf

/-- What `bytes.Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically
less than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`). -/
def compareResult (a b : List w8) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

end wps

end bytes

end Perennial
