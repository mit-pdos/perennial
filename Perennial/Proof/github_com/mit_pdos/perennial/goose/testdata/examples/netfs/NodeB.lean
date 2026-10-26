/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs.NodeB`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write
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

/-- `"b"` reads `"sent"` under the invariant of its files. If it is marked, the
files are done, so `"out"` is `c0`, which `"b"` sends. Otherwise `"b"` receives
`c0` from `"a"` (`recvFrom`), writes it to `"out"` (the files are done, with
the witness), marks `"sent"` (allowed by the witness) and sends `c0`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.wp_proof
    (wp_Read : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write.spec (GF := GF) (hG := hG))
    (wp_Send : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send.spec (GF := GF) (hG := hG))
    (wp_recvFrom : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.recvFrom.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.spec (GF := GF) (hG := hG) := fun c0 γ HB => by
  have wp_Read' := fun name =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read) (type_args := [])) ▸ wp_Read name
  have wp_Write' := fun name data =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write) (type_args := [])) ▸ wp_Write name data
  have wp_Send' := fun to sl data dq =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Send) (type_args := [])) ▸ wp_Send to sl data dq
  wp_start as ⟨#Hinv, #Hb⟩
  try wp_auto
  -- read `"sent"`
  wp_func_call
  wp_apply_core wp_Read' go!"sent"
  imod bInv_read_sent c0 γ $$ Hb with ⟨%q, %ss, Hsent, Hclose⟩
  imodintro
  iexists q, ss
  iframe Hsent
  iintro Hsent
  imod Hclose $$ Hsent with #Hd
  imodintro
  try wp_auto
  wp_if_destruct
  · -- marked: `"out"` is `c0`
    ihave #Hd := Hd $$ []
    · ipureintro; simp
    wp_func_call
    wp_apply_core wp_Read' go!"out"
    imod bInv_read_out c0 γ $$ Hd Hb with ⟨%q, Hout, Hclose⟩
    imodintro
    iexists q, c0
    iframe Hout
    iintro Hout
    imod Hclose $$ Hout
    imodintro
    try wp_auto
    wp_apply wp_string_to_bytes c0 with %sl ⟨Hsl, Hcap⟩
    wp_func_call
    wp_apply_core wp_Send' go!"a" sl c0 (DFrac.own 1) $$ Hsl
    imod netInv_send c0 go!"a" c0 (.inl rfl) (fun _ => rfl) $$ Hinv with ⟨%ms, Ha, Hclose⟩
    imodintro
    iexists ms
    iframe Ha
    iintro Ha
    imod Hclose $$ Ha
    imodintro
    iintro Hsl
    try wp_auto
    iapply HΦ
    itrivial
  · -- not marked: receive from `"a"`
    wp_apply wp_recvFrom c0 go!"a" (by decide) (.inr HB) $$ [] with %sl Hsl
    · iframe Hinv
    wp_apply wp_bytes_to_string sl c0 (DFrac.own 1) $$ Hsl with Hsl
    try wp_auto
    -- write `"out"`
    wp_func_call
    wp_apply_core wp_Write' go!"out" c0
    imod bInv_write_out c0 γ $$ Hb with ⟨%old, Hout, Hclose⟩
    imodintro
    iexists old
    iframe Hout
    iintro Hout
    imod Hclose $$ Hout with #Hd'
    imodintro
    try wp_auto
    -- mark `"sent"`
    wp_func_call
    wp_apply_core wp_Write' go!"sent" go!"yes"
    imod bInv_write_sent c0 γ $$ Hd' Hb with ⟨%old, Hsent, Hclose⟩
    imodintro
    iexists old
    iframe Hsent
    iintro Hsent
    imod Hclose $$ Hsent
    imodintro
    try wp_auto
    -- send it back to `"a"`
    wp_apply wp_string_to_bytes c0 with %sl' ⟨Hsl', Hcap'⟩
    wp_func_call
    wp_apply_core wp_Send' go!"a" sl' c0 (DFrac.own 1) $$ Hsl'
    imod netInv_send c0 go!"a" c0 (.inl rfl) (fun _ => rfl) $$ Hinv with ⟨%ms, Ha, Hclose⟩
    imodintro
    iexists ms
    iframe Ha
    iintro Ha
    imod Hclose $$ Ha
    imodintro
    iintro Hsl'
    try wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
