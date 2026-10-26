/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.send`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.send_

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

/-- `send` is the network's send (`Perennial/TrustedCode/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/netext.lean`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.send.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.send.spec (GF := GF) (hG := hG) := fun to data => by
  iintro %Φ HAU
  wp_func_call
  unfold send.impl
  wp_pures
  iapply wp_NetSend_atomic $$ HAU

end proof

end Perennial
