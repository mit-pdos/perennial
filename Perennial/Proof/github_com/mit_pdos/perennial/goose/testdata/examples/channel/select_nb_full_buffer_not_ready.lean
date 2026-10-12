/-
The proof of `channel.select_nb_full_buffer_not_ready`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_full_buffer_not_ready
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.SelectTrickyDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_full_buffer_not_ready.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.select_nb_full_buffer_not_ready.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make2 (V := w64) (W64 1) $$ [] as %ch %γ ⟨#His_chan, %Hcap, Hown⟩
  · ipureintro; decide
  -- First send: use the empty-buffer AU to fill buffer to [0].
  wp_apply_core chan.wp_send ch (W64 0) γ $$ His_chan
  iintro -
  iapply SendAU_from_empty_buffer_to ch γ $$ Hown
  -- Now we have: ownChan (Buffered [0]) in the continuation.
  iintro Hoc
  imod start_select_nb_full1 ch γ $$ His_chan [] Hoc with Hfull
  · ipureintro; exact Hcap
  wp_auto
  -- Nonblocking select: show send case is disabled -> default taken.
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ, W64 0
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iexact His_chan
    -- AU for send case: forced not-ready by full-buffer invariant.
    iapply select_nb_full1_send_au γ ch $$ Hfull []
    itrivial
  · -- default branch
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
