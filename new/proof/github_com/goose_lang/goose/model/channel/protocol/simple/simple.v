Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import
  chan_au_send chan_au_recv chan_au_base.

(** * Simple Channel Pattern Verification

    This file provides verification for the "simple" pattern - a channel with a
    predicate P over values sent on the channel.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.

Record simple_names := {
  chan_name : chan_names;
}.

Definition is_simple (γ : simple_names) (ch : loc) (P : V → iProp Σ) : iProp Σ :=
  ∃ cap,
  "#Hch" ∷ is_channel ch cap γ.(chan_name) ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chan_rep.t V),
      "Hch" ∷ own_channel ch cap s γ.(chan_name) ∗
      match s with
      | chan_rep.Idle => True
      | chan_rep.SndPending v => P v
      | chan_rep.SndCommit v => P v
      | chan_rep.Buffered vs => [∗ list] v ∈ vs, P v
      | chan_rep.Closed buffer => False
      | _ => True
      end
  )%I.
#[global] Opaque is_simple.
#[local] Transparent is_simple.

Lemma start_simple (ch : loc) (cap : Z) (γ : chan_names) (P : V → iProp Σ) :
  is_channel ch cap γ -∗
  own_channel ch cap chan_rep.Idle γ ={⊤}=∗
  ∃ γdone, is_simple γdone ch P.
Proof.
  iIntros "#Hch Hoc".
  iExists {|
    chan_name := γ;
  |}.
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  simpl.
  by iFrame "#".
Qed.

Lemma wp_simple_receive γ ch P :
  {{{ is_pkg_init channel ∗
      is_simple γ ch P }}}
    ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #()
  {{{ v, RET (#v, #true); P v }}}.
Proof.
  wp_start_folded as "#Hsimple".
  unfold is_simple. iNamed "Hsimple".
  iApply wp_fupd.
  wp_apply (wp_Receive ch cap γ.(chan_name) with "[$Hch]").
  iIntros "(? & ? & ? & ?)".
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
    unfold rcv_au_inner.
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
      iModIntro. iModIntro.
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
    iModIntro. iModIntro.
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

Lemma wp_simple_send γ ch v P :
  {{{ is_pkg_init channel ∗
      is_simple γ ch P ∗
      P v }}}
    ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "[#Hsimple HP]".
  unfold is_simple. iNamed "Hsimple".
  iApply wp_fupd.
  wp_apply (wp_Send ch cap with "[$Hch]").
  iIntros "(? & ? & ? & ?)".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.

    destruct (Z.ltb_spec (length buff) cap).
    {
      iIntros "Hoc".
      iMod "Hmask" as "_".
      iMod ("Hinv_close" with "[Hoc Hinv_open HP]") as "_".
      {
        iNext. iFrame.
        rewrite big_sepL_app /=.
        iFrame.
      }
      iModIntro. iModIntro.
      iApply "HΦ".
      iFrame.
    }
    done.
  }
  {
    iFrame.
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
    unfold send_au_inner.
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
      iModIntro. iModIntro.
      iApply "HΦ".
      iFrame.
    }
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
    iMod ("Hinv_close" with "[Hoc HP]") as "_".
    {
      iNext. iFrame. done.
    }
    iModIntro. iModIntro.
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
Qed.

End proof.
