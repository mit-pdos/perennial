From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require Import channel_examples_init.
From New.golang.theory.chan.idioms
  Require Import base.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Invariant: channel must be Idle, all other states are False *)
Definition is_select_nb_only (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ s,
        "Hoc" ∷ own_chan γ unit s ∗
        "%" ∷ ⌜ (match s with
                | chanstate.Idle => True
                | _ => False
                end) ⌝
  ).

Lemma start_select_nb_only (ch : loc) (γ : chan_names) :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={⊤}=∗
  is_select_nb_only γ ch.
Proof.
  iIntros "#Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  iFrame "#". done.
Qed.

(** Nonblocking send AU - vacuous since we ban all send preconditions *)
Lemma select_nb_only_send_au γ ch (v : unit) :
  ∀ Φ Φnotready,
  is_select_nb_only γ ch -∗
  Φnotready -∗
  nonblocking_send_au γ v Φ Φnotready.
Proof.
  iIntros (Φ Φnotready) "#Hnb Hnotready".
  iNamed "Hnb". iSplit. all: try done.
  iInv "Hinv" as ">Hinv_open" "Hinv_close". iNamed "Hinv_open".
  destruct s; try done.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iFrame.
Qed.


(** Nonblocking receive AU - vacuous since we ban all receive preconditions *)
Lemma select_nb_only_rcv_au γ ch :
   ∀ (Φ: unit → bool → iProp Σ) (Φnotready: iProp Σ),
  is_select_nb_only γ ch -∗
  Φnotready -∗
  nonblocking_recv_au γ unit (λ (v:unit) (ok:bool), Φ v ok) Φnotready.
Proof.
  iIntros (Φ Φnotready) "#Hnb Hnotready".
  iNamed "Hnb".
  iSplit. all: try done.
  iInv "Hinv" as ">Hinv_open" "Hinv_close".
  iNamed "Hinv_open". destruct s; try done.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iFrame.
Qed.


(* Example 1 *)
Lemma wp_select_nb_not_ready :
  {{{ is_pkg_init channel_examples}}}
    @! channel_examples.select_nb_not_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#His_chan & _Hcap & Hownchan)".
  do 2 (iRename select (£1) into "Hlc1").
  wp_auto_lc 2.
  iRename select (£1) into "Hlc2".
  iPersist "ch".
  do 2 (iRename select (£1) into "Hlc4").
  iMod (start_select_nb_only ch with "[$His_chan] [$Hownchan]") as "#Hnb".
  wp_apply (wp_fork with "[Hnb]").
  {
  wp_auto_lc 4.
  wp_apply chan.wp_select_nonblocking.
  simpl. iSplitL.
  - (* Prove the receive case - will be vacuous *)
    iSplitL. all: try done.
    repeat iExists _; iSplitR; first done.
    (* extract is_chan *)
    iPoseProof "Hnb" as "[$ _]".
    (* Now use our select_nb_only_rcv_au lemma *)
    iRename select (£1) into "Hlc1".
    iApply (select_nb_only_rcv_au with " [$Hnb]");first done.
  - (* Prove the default case *)
    wp_auto.
    done.
  }
  {
  wp_apply chan.wp_select_nonblocking. simpl.
  iFrame.
  iSplitL "Hlc1 Hlc4".
  - (* Prove the receive case - will be vacuous *)
    iSplitL; last done.
    repeat iExists _; iSplitR; first done. iFrame "#". iClear "His_chan".
    iApply (select_nb_only_send_au with "[$Hnb] []"); first done.
  - (* Prove the default case *)
    wp_auto.
    iApply "HΦ".
    done.
  }
Qed.

(**  Example 2 *)
Lemma wp_select_nb_guaranteed_ready :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.select_nb_guaranteed_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros "* (#His_ch & %Hcap & Hch)". simpl.
  wp_auto.
  wp_apply (chan.wp_close with "[$]").
  iIntros "_". iApply fupd_mask_intro; first solve_ndisj.
  iIntros "Hmask". iFrame. iNext. iIntros "Hch". iMod "Hmask" as "_". iModIntro.
  wp_auto.
  wp_apply (chan.wp_select_nonblocking_alt [False%I] with "[Hch] [-]");
    [|iNamedAccu|].
  - simpl. iSplitL; last done. iIntros "HP". repeat iExists _; iSplitR; first done. iFrame "#".
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iFrame. iIntros "!> Hch". iMod "Hmask" as "_". iModIntro.
    iNamed "HP". wp_auto. by iApply "HΦ".
  - iNamed 1. simpl. iIntros ([[]]).
Qed.

(* Invariant for the "full buffer" situation                                  *)
Definition is_select_nb_full1 (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch"  ∷ is_chan ch γ w64 ∗
  "%Hcap1" ∷ ⌜chan_cap γ = (W64 1)⌝ ∗
  "#Hinv" ∷ (own_chan γ w64 (chanstate.Buffered [W64 0])).

Lemma start_select_nb_full1 (ch : loc) (γ : chan_names) :
  is_chan ch γ w64 -∗
  ⌜chan_cap γ = (W64 1)⌝ -∗
  own_chan γ w64 (chanstate.Buffered [W64 0]) ={⊤}=∗
  is_select_nb_full1 γ ch.
Proof.
  iIntros "#Hch %Hcap Hoc".
  iModIntro. iFrame "#". iFrame "%". iFrame.
Qed.

Lemma select_nb_full1_send_au (γ : chan_names) (ch : loc) :
  ∀ Φ Φnotready,
    is_select_nb_full1 γ ch -∗
    Φnotready -∗
    nonblocking_send_au γ (W64 0) Φ Φnotready.
Proof.
  intros Φ Φnotready.
  iIntros "Hfull Hnotready".
  iNamed "Hfull".
  iSplit; last done.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.

  iExists (chanstate.Buffered [W64 0]).
  iFrame.
  iIntros "Hoc'".
  (* Show this contradicts the capacity bound. *)
  iPoseProof (own_chan_buffer_size with "Hoc'") as "%Hle".
  rewrite Hcap1 in Hle.
  done.
Qed.

Lemma SendAU_from_empty_buffer_to
    (ch: loc) (γ: chan_names) (Φ : iProp Σ) :
  own_chan γ w64 (chanstate.Buffered []) -∗
  (own_chan γ w64 (chanstate.Buffered [W64 0]) -∗ Φ) -∗
  send_au γ (W64 0) Φ.
Proof.
  iIntros "Hoc Hk".
  unfold send_au.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.
  iExists (chanstate.Buffered []).
  iFrame "Hoc".
  simpl.
  iIntros "Hoc'".
  iMod "Hmask".
  iApply ("Hk" with "Hoc'").
Qed.

(*
  From a send on full buffer (which blocks indefinitely), any Φ can be derived
*)
Lemma SendAU_full_cap1_vacuous
  (ch : loc) (γ : chan_names) (v0 v : w64) (Φ : iProp Σ) :
  chan_cap γ = (W64 1) ->
  own_chan γ w64 (chanstate.Buffered [v0]) -∗
  send_au γ v Φ.
Proof.
  intros Hcap.
  iIntros "Hoc".
  unfold send_au.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.
  iExists (chanstate.Buffered [v0]).
  iFrame "Hoc".
  simpl.
  iIntros "Hoc'".
  iPoseProof (own_chan_buffer_size with "Hoc'") as "%Hle".
  rewrite Hcap in Hle.
  done.
Qed.

(* Example 3 *)
Lemma wp_select_nb_full_buffer_not_ready :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.select_nb_full_buffer_not_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2.

  wp_apply (chan.wp_make2); first done.
  iIntros (ch γ) "(#His_chan & %Hcap & Hown)".
  wp_auto.

  (* First send: use the empty-buffer AU to fill buffer to [0]. *)
  wp_apply (chan.wp_send ch (W64 0) γ with "[$His_chan]").
  iIntros "Hlc_send". simpl.
  iApply ((SendAU_from_empty_buffer_to ch γ) with "Hown").

  (* Now we have: own_chan ch (Buffered [0]) γ in the continuation. *)
  iIntros "Hoc".
  iMod (start_select_nb_full1 ch γ with "[$His_chan] [%] [$Hoc]") as "Hfull".
{ exact Hcap. }  (* supplies ⌜chan_cap γ = 1⌝ *)
wp_auto.

  (* Nonblocking select: show send case is disabled -> default taken. *)
  wp_apply chan.wp_select_nonblocking.

  iSplit.
  - simpl. iSplit; last done.
    iExists w64, ch,γ, (W64 0). repeat iExists _.

    iSplit; [iPureIntro; split;first done;reflexivity|].
    iSplit; [iFrame "#"; done|].
    (* AU for send case: forced not-ready by full-buffer invariant.
      => We can get contradiction
    *)
    iApply (select_nb_full1_send_au γ ch with "[$Hfull]").
    all:try done.
  - (* default branch *)
    wp_auto. iApply "HΦ". done.
    Unshelve.
    + apply sem.
    + apply _.
Qed.

End proof.
