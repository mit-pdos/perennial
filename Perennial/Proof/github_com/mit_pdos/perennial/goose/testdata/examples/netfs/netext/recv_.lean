/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.recv`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.recv_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode net_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Assumptions]

/-- `recv` is the network's receive (`Perennial/TrustedCode/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/netext.lean`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.recv.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.recv.spec (GF := GF) (hG := hG) := by
  iintro %Φ HAU
  wp_func_call
  unfold recv.impl
  wp_pures
  iapply wp_NetRecv_atomic $$ HAU

end proof

end Perennial
