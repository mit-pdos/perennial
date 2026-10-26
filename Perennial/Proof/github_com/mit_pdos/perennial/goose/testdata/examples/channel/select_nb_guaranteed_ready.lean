/-
The proof of `channel.select_nb_guaranteed_ready`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_guaranteed_ready
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.SelectTrickyDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_guaranteed_ready.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_guaranteed_ready.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make1 (V := w64) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  wp_apply_core chan.wp_close (V := w64) ch γ $$ His_ch
  iintro -
  unfold closeAu
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Idle
  iframe Hch
  dsimp only
  iintro Hch
  imod Hmask with -
  imodintro
  wp_auto
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)] (ownChan γ w64 (.Closed [])) $$ [HΦ] Hch []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro HP
    simp only [chan.nonblockingAltClausePre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact His_ch
    unfold nonblockingRecvAuAlt
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Closed []
    iframe HP
    dsimp only
    iintro Hch
    imod Hmask with -
    imodintro
    wp_auto
    iapply HΦ
    itrivial
  · iintro - Hnr
    icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hf
    iexfalso; iexact Hf

end proof

end Perennial
