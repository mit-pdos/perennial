/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs.Main`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write

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

/-- Each call of `fsext` opens the invariant of the file for its step. The
first read learns that the file is `""` or `"done"`; both branches of the `if`
end with the witness that it is done (the write produces it), so the second
read returns `"done"`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main.wp_proof
    (wp_Read : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main.spec (GF := GF) (hG := hG) := fun N γ => by
  -- the specs for the functions' implementations, to which `wp_pures` and
  -- `wp_func_call` resolve the calls
  have wp_Read' := fun name =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read) (type_args := [])) ▸ wp_Read name
  have wp_Write' := fun name data =>
    (FuncUnfold.func_unfold (f := github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write) (type_args := [])) ▸ wp_Write name data
  wp_start as #Hinv
  wp_func_call
  wp_pures
  -- the first read
  wp_apply_core wp_Read' go!"f"
  iinv Hinv with ⟨%c, >Hf, >Hc⟩ Hclose
  icases fileState_read γ c $$ Hc with ⟨%Hgood, #Hdone, Hc⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), c
  iframe Hf
  iintro Hf
  imod Hmask with -
  imod Hclose $$ [Hf Hc] with -
  · inext; iexists c; iframe
  imodintro
  wp_auto
  wp_join iprop(fileDone γ) with [-HΦ] as #Hd
  · -- `s == ""`: the write
    wp_func_call
    wp_apply_core wp_Write' go!"f" go!"done"
    iinv Hinv with ⟨%c, >Hf, >Hc⟩ Hclose
    imod fileState_write γ c $$ Hc with ⟨#Hd, Hc⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists c
    iframe Hf
    iintro Hf
    imod Hmask with -
    imod Hclose $$ [Hf Hc] with -
    · inext; iexists go!"done"; iframe
    imodintro
    wp_auto
    wp_join_done
    iexact Hd
  · -- `s != ""`: then the file is `"done"`, and the first read saw the witness
    obtain rfl : c = go!"done" := Hgood.resolve_left Hif
    wp_auto
    wp_join_done
    iapply Hdone $$ %rfl
  -- the second read
  wp_func_call
  wp_apply_core wp_Read' go!"f"
  iinv Hinv with ⟨%c, >Hf, >Hc⟩ Hclose
  icases fileState_done γ c $$ Hd Hc with ⟨%Hc', Hc⟩
  subst Hc'
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), go!"done"
  iframe Hf
  iintro Hf
  imod Hmask with -
  imod Hclose $$ [Hf Hc] with -
  · inext; iexists go!"done"; iframe
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
