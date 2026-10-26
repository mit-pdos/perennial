/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeA`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom

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

/-- `"a"` reads `c0` from its file, sends it to `"b"` (following the protocol)
and receives `c0` back from `"b"` (`recvFrom`), so the check passes. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA.wp_proof
    (wp_Read : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read.spec (GF := GF) (hG := hG))
    (wp_Send : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.spec (GF := GF) (hG := hG))
    (wp_recvFrom : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA.spec (GF := GF) (hG := hG) := fun c0 HA => by
  have wp_Read' := fun name =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read) (type_args := [])) ▸ wp_Read name
  have wp_Send' := fun to sl data dq =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send) (type_args := [])) ▸ wp_Send to sl data dq
  wp_start as ⟨#Hinv, #Hin⟩
  try wp_auto
  -- read the file
  wp_func_call
  wp_apply_core wp_Read' go!"in"
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists DFrac.discard, c0
  iframe Hin
  iintro _
  imod Hmask
  imodintro
  try wp_auto
  -- send it to `"b"`
  wp_apply wp_string_to_bytes c0 with %sl ⟨Hsl, Hcap⟩
  wp_func_call
  wp_apply_core wp_Send' go!"b" sl c0 (DFrac.own 1) $$ Hsl
  imod netInv_send c0 go!"b" c0 (.inr rfl) (fun _ => rfl) $$ Hinv with ⟨%ms, Hb, Hclose⟩
  imodintro
  iexists ms
  iframe Hb
  iintro Hb
  imod Hclose $$ Hb
  imodintro
  iintro Hsl
  try wp_auto
  -- receive the reply
  wp_apply wp_recvFrom c0 go!"b" (by decide) (.inl HA) $$ [] with %sl' Hsl'
  · iframe Hinv
  wp_apply wp_bytes_to_string sl' c0 (DFrac.own 1) $$ Hsl' with Hsl'
  try wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
