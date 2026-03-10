Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import
  chan_au_base.
Require Import New.golang.theory.

(** * "Bag" channel specification.

    This channel spec has a user-chosen predicate P over values sent on the
    channel, but no ordering guarantees. It's like a "bag" of values, with
    `send` inserting and `receive` removing.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Collection W := sem + IntoValTyped0.

Definition is_chan_bag (γ : chan_names) (ch : loc) (P : V → iProp Σ) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ V ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chanstate.t V),
      "Hch" ∷ own_chan γ V s ∗
      match s with
      | chanstate.Idle => True
      | chanstate.SndPending v => P v
      | chanstate.SndCommit v => P v
      | chanstate.Buffered vs => [∗ list] v ∈ vs, P v
      | chanstate.Closed buffer => False
      | _ => True
      end
  )%I.
#[global] Opaque is_chan_bag.
#[local] Transparent is_chan_bag.
#[global] Instance is_chan_bag_pers γ ch P : Persistent (is_chan_bag γ ch P).
Proof. apply _. Qed.

Lemma start_bag (P : V → iProp Σ) s (ch : loc) (γ : chan_names)  :
  match s with
  | chanstate.Idle | chanstate.Buffered [] => True
  | _ => False
  end →
  is_chan ch γ V -∗
  own_chan γ V s ={⊤}=∗
  is_chan_bag γ ch P.
Proof.
  iIntros "% #Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. destruct s; try destruct buff; done. }
  simpl.
  by iFrame "#".
Qed.

Lemma is_bag_is_chan γ ch P :
  is_chan_bag γ ch P -∗ is_chan ch γ V.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma bag_recv_au γ ch P Φ  :
  £1 ∗ £1  -∗
  is_chan_bag γ ch P -∗
  (▷ ∀ v, P v -∗ Φ v true ) -∗
  recv_au γ V Φ.
Proof.
  iIntros "(? & ? ) #Hbag HΦ".
  iNamed "Hbag".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    destruct buff as [|v0 buff']; [ done | ].
    iIntros "Hoc".
    rewrite big_sepL_cons.
    iDestruct "Hinv_open" as "[HP Hinv_open]".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc Hinv_open]") as "_".
    {
      iNext. iFrame. done.
    }
    iModIntro.
    iApply "HΦ".
    iFrame. }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    {
      iNext. iFrame.
    }
    iModIntro.
    unfold recv_nested_au.
    iInv "Hinv" as "Hinv_open1" "Hinv_close".
    iMod (lc_fupd_elim_later with "[$] Hinv_open1") as "Hinv_open1".
    iNamed "Hinv_open1".
    destruct s; try done.
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
      iIntros "Hoc".
      iMod "Hmask" as "_".
      iMod ("Hinv_close" with "[Hoc]") as "_".
      {
        iNext. iFrame.
      }
      iModIntro.
      iApply "HΦ".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    {
      iNext. iFrame.
    }
    iModIntro.
    iApply "HΦ".
    iFrame.
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
  }
Qed.

Lemma wp_bag_receive γ ch P :
  {{{ is_chan_bag γ ch P }}}
    chan.receive t #ch
  {{{ v, RET (#v, #true); P v }}}.
Proof using W.
  wp_start_folded as "#Hbag".
  iNamed "Hbag".
  wp_apply (chan.wp_receive ch γ with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (bag_recv_au with "[$]").
  {
    iFrame "#".
  }
  {
   iNext. iFrame.
  }
Qed.

Lemma bag_send_au γ ch P v (Φ: iProp Σ) :
  £1 ∗ £1 -∗
  is_chan_bag γ ch P -∗
  P v -∗
  (▷ Φ) -∗
  send_au γ v Φ.
Proof.
  iIntros "(? & ?) #Hbag HP HΦ".
  iNamed "Hbag".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  - iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc Hinv_open HP]") as "_".
    {
      iNext. iFrame.
      rewrite big_sepL_app /=.
      iFrame.
    }
    iModIntro.
    done.
  - iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc HP]") as "_".
    {
      iNext. iFrame.
      simpl. iFrame.
    }
    iModIntro.
    unfold send_nested_au.
    iInv "Hinv" as "Hinv_open1" "Hinv_close".
    iMod (lc_fupd_elim_later with "[$] Hinv_open1") as "Hinv_open1".
    iNamed "Hinv_open1".
    destruct s; try done.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    + iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
      iIntros "Hoc".
      iMod "Hmask" as "_".
      iMod ("Hinv_close" with "[Hoc]") as "_".
      {
        iNext. iFrame.
      }
      done.

  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.

  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc HP]") as "_".
    {
      iNext. iFrame. done.
    }
    iModIntro.
    done.

  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.

  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
Qed.

Lemma wp_bag_send γ ch v P :
  {{{ is_chan_bag γ ch P ∗ P v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof using W.
  wp_start_folded as "[#Hbag HP]".
  unfold is_chan_bag. iNamed "Hbag".
  wp_apply (chan.wp_send ch with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & ? & ?)".
  iApply (bag_send_au with "[$] [$] [$HP]").
  wp_end.
Qed.

End proof.
