/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeC`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send

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

/-- `"c"`'s messages follow the protocol, whatever their data: they are from `"c"`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC.wp_proof
    (wp_Send : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC.spec (GF := GF) (hG := hG) := fun c0 HC => by
  have wp_Send' := fun to sl data dq =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send) (type_args := [])) ▸ wp_Send to sl data dq
  wp_start as #Hinv
  try wp_auto
  wp_apply wp_string_to_bytes go!"junk" with %sl ⟨Hsl, Hcap⟩
  wp_func_call
  wp_apply_core wp_Send' go!"a" sl go!"junk" (DFrac.own 1) $$ Hsl
  imod netInv_send c0 go!"a" go!"junk" (.inl rfl) (fun h => absurd HC h) $$ Hinv
    with ⟨%ms, Ha, Hclose⟩
  imodintro
  iexists ms
  iframe Ha
  iintro Ha
  imod Hclose $$ Ha
  imodintro
  iintro Hsl
  try wp_auto
  wp_apply wp_string_to_bytes go!"junk" with %sl' ⟨Hsl', Hcap'⟩
  wp_func_call
  wp_apply_core wp_Send' go!"b" sl' go!"junk" (DFrac.own 1) $$ Hsl'
  imod netInv_send c0 go!"b" go!"junk" (.inr rfl) (fun h => absurd HC h) $$ Hinv
    with ⟨%ms', Hb, Hclose⟩
  imodintro
  iexists ms'
  iframe Hb
  iintro Hb
  imod Hclose $$ Hb
  imodintro
  iintro Hsl'
  try wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
