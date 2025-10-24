From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base chan_au_send chan_au_recv simple.
From New.proof Require Import time sync.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.
Context `{!chanGhostStateG Σ slice.t}.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Definition search_replace (x y: w64) : list w64 → list w64 :=
  fmap (λ a, if decide (a = x) then y else a).

Definition chanP (x y: w64) (s: slice.t) : iProp Σ :=
  (* TODO: somehow this slice needs to be exactly the data in some subslice of
  the original list; does that need to be connected with a ghost variable? *)
  ∃ (xs: list w64), s ↦* xs
  (* TODO: need permission to send back ownership of s ↦* search_replace x y
  xs on the waitgroup *)
.

Definition waitgroupN := nroot .@ "waitgroup".

Lemma wp_worker (γs: simple_names) (γwg: WaitGroup_names) (ch: loc) (wg: loc) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
        "#Hchan" ∷ is_simple γs ch 4 (chanP x y) ∗
        "Hwg" ∷ is_WaitGroup wg γwg waitgroupN }}}
    @! chan_spec_raw_examples.worker #ch #wg #x #y
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_simple_receive with "[$Hchan]").
  iIntros (s) "Hrcv".
  iDestruct "Hrcv" as (xs) "Hs".
  wp_auto.
  wp_for.
  (* TODO: prove inner loop does search-replace for s *)
Admitted.

Lemma wp_SearchReplace (s: slice.t) (xs: list w64) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ s ↦* xs }}}
    @! chan_spec_raw_examples.SearchReplace #s #x #y
  {{{ RET #(); s ↦* (search_replace x y xs) }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_if_destruct.
  {
    assert (length xs = 0%nat) by word.
    destruct xs; simpl in *; [ | congruence ].
    iApply "HΦ".
    iFrame.
  }
  wp_apply wp_NewChannelRef.
  { done. }
  iIntros (ch γch_names) "[#His_chan Hoc]".
  change (4 =? 0) with false; simpl.
  iMod (start_simple_buffered _ _ _ (chanP x y) with "[$His_chan] [$Hoc]") as (γch) "#Hchan".
  wp_auto.
Admitted.

End proof.
