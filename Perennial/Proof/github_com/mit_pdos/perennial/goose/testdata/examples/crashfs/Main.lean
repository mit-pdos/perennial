/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs.Main`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Read
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Assumptions]

/-- Each call of `fsffi` opens the invariant of the file for its step. The
first read learns that the file is `""` or `"done"`; both branches of the `if`
end with the witness that it is done (the write produces it), so the second
read returns `"done"`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main.wp_proof
    (wp_Read : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Read.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main.spec (GF := GF) (hG := hG) := fun N γ => by
  -- the specs of the calls, for the functions' implementations (`wp_pures` resolves
  -- a call to its implementation, `wp_func_call` too)
  have wp_Read' := fun name => (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Read) (type_args := [])) ▸
    wp_Read name
  have wp_Write' := fun name data =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write) (type_args := [])) ▸ wp_Write name data
  wp_start as #Hinv
  wp_func_call
  wp_pures
  -- the first read
  try wp_func_call
  wp_apply_core wp_Read' go!"f"
  iinv Hinv with Hi Hclose
  try unfold fileInv
  icases Hi with ⟨%c, >Hf, >Hc⟩
  icases fileInv_cases γ c $$ Hc with ⟨%Hgood, #Hdone, Hc⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), c
  iframe Hf
  iintro Hf
  imod Hmask with -
  imod Hclose $$ [Hf Hc] with -
  · inext; try unfold fileInv
    iexists c; iframe
  imodintro
  wp_auto
  wp_join iprop(dghostVar γ .discard ()) with [-HΦ] as #Hd
  · -- `s == ""`: the write
    try wp_func_call
    wp_apply_core wp_Write' go!"f" go!"done"
    iinv Hinv with Hi Hclose
    try unfold fileInv
    icases Hi with ⟨%c2, >Hf, >Hc⟩
    imod fileInv_witness γ c2 $$ Hc with #Hd
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists c2
    iframe Hf
    iintro Hf
    imod Hmask with -
    imod Hclose $$ [Hf] with -
    · inext; try unfold fileInv
      iexists go!"done"; iframe Hf; iright; isplitr
      · ipureintro; rfl
      iexact Hd
    imodintro
    wp_auto
    wp_join_done
    iexact Hd
  · -- `s != ""`: then `s` is `"done"`, and the first read saw the witness
    obtain rfl : c = go!"done" := Hgood.resolve_left Hif
    ihave #Hd := Hdone $$ %rfl
    wp_auto
    wp_join_done
    iexact Hd
  -- the second read
  try wp_func_call
  wp_apply_core wp_Read' go!"f"
  iinv Hinv with Hi Hclose
  try unfold fileInv
  icases Hi with ⟨%c3, >Hf, >Hc⟩
  icases fileInv_done γ c3 $$ Hd Hc with ⟨%Hc3, Hc⟩
  subst Hc3
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), go!"done"
  iframe Hf
  iintro Hf
  imod Hmask with -
  imod Hclose $$ [Hf Hc] with -
  · inext; try unfold fileInv
    iexists go!"done"; iframe
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
