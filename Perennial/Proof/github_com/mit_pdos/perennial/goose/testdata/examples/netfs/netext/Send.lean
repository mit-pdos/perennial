/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext.Send`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.wp_proof
    (wp_send : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.send.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.spec (GF := GF) (hG := hG) := fun to sl data dq => by
  have wp_send' := fun to data =>
    (FuncUnfold.func_unfold (f := send) (type_args := [])) ▸ wp_send to data
  iintro %Φ Hsl HAU
  wp_func_call
  unfold Send.impl
  wp_auto
  wp_apply wp_bytes_to_string sl data dq $$ Hsl with Hsl
  try wp_auto
  wp_func_call
  wp_apply_core wp_send' to data
  imod HAU with ⟨%ms, Hto, Hclose⟩
  imodintro
  iexists ms
  iframe Hto
  iintro Hto
  imod Hclose $$ Hto with HΦ
  imodintro
  wp_auto
  iapply HΦ $$ Hsl

end proof

end Perennial
