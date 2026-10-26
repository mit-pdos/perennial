/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.Recv`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv.wp_proof
    (wp_recv : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.recv.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv.spec (GF := GF) (hG := hG) := by
  unfold recv.spec at wp_recv
  have wp_recv' := (FuncUnfold.func_unfold (f := recv) (type_args := [])) ▸ wp_recv
  iintro %Φ HAU
  wp_func_call
  unfold Recv.impl
  wp_auto
  wp_func_call
  wp_apply_core wp_recv'
  imod HAU with ⟨%q, %ms, Hme, Hclose⟩
  imodintro
  iexists q, ms
  iframe Hme
  iintro %m %Hm Hme
  imod Hclose $$ %m %Hm Hme with HΦ
  imodintro
  wp_auto
  wp_apply wp_string_to_bytes m.data with %sl ⟨Hsl, Hcap⟩
  iapply HΦ $$ Hsl Hcap

end proof

end Perennial
