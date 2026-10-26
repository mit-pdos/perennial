/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs.recvFrom`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext net_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Assumptions]

/-- Each receive opens the protocol's invariant: a message from `peer`, which is
not `"c"`, carries `c0`; a message from another node is ignored. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom.wp_proof
    (wp_Recv : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom.spec (GF := GF) (hG := hG) := fun c0 peer Hpeer Hme => by
  unfold github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv.spec at wp_Recv
  have wp_Recv' := (FuncUnfold.func_unfold
    (f := github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Recv) (type_args := [])) ▸ wp_Recv
  wp_start as #Hinv
  wp_auto
  wp_for
  wp_func_call
  wp_apply_core wp_Recv'
  imod netInv_recv c0 Hme $$ Hinv with ⟨%q, %ms, Hme', Hclose⟩
  imodintro
  iexists q, ms
  iframe Hme'
  iintro %m %Hm Hme'
  imod Hclose $$ %m %Hm Hme' with %Hgood
  imodintro
  iintro %sl Hsl Hcap
  wp_auto
  wp_if_destruct
  · -- from `peer`: the data is `c0`
    wp_for_post
    iapply HΦ
    rw [← Hgood Hpeer]
    iexact Hsl
  · -- from another node: wait for the next message
    wp_for_post
    iframe

end proof

end Perennial
