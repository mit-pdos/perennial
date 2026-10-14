/-
The proof of `channel.select_nb_not_ready`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_not_ready
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.SelectTrickyDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_not_ready.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_not_ready.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_chan, -, Hownchan⟩
  imod start_select_nb_only ch γ $$ His_chan Hownchan with #Hnb
  ipersist ch
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_singleton.2
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact His_chan
      iapply select_nb_only_rcv_au $$ Hnb []
      itrivial
    · wp_auto
      itrivial
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iexact His_chan
    iapply select_nb_only_send_au $$ Hnb []
    itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
