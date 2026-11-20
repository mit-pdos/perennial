/-
Shared definitions of the proofs of `internal/strconv`: its `isPkgInit`, and the model of
`ParseBool`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.strconv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.strconv

/-- The boolean `ParseBool` reads from a string: `1`, `t`, `T`, `TRUE`, `true`, `True` are
true, `0`, `f`, `F`, `FALSE`, `false`, `False` false; any other string is an error. -/
def parseBool (s : GoString) : Option Bool :=
  if s ∈ [go!"1", go!"t", go!"T", go!"true", go!"TRUE", go!"True"] then some true
  else if s ∈ [go!"0", go!"f", go!"F", go!"false", go!"FALSE", go!"False"] then some false
  else none

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.strconv :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.strconv :=
  build_get_is_pkg_init_wf

end wps

end internal.strconv

end Perennial
