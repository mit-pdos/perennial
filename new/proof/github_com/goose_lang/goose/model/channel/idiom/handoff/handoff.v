From New.proof.github_com.goose_lang.goose.model.channel Require Import
  chan_au_base.
Require Import New.golang.theory.
Require Import New.proof.proof_prelude.

(** * Handoff Channel Pattern Verification

    This file provides verification for the "handoff" pattern - a channel with a
    predicate P over values sent on the channel.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!allG Σ].
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

Record handoff_names := {
  chan_name : chan_names;
}.

(* TODO: should not have to be exposed *)
Definition is_chan_handoff (γ : handoff_names) (ch : loc) (P : V → iProp Σ) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ.(chan_name) V ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chanstate.t V),
      "Hch" ∷ own_chan γ.(chan_name) V s ∗
      match s with
      | chanstate.Idle => True
      | chanstate.SndPending v => P v
      | chanstate.SndCommit v => P v
      | chanstate.Buffered vs => [∗ list] v ∈ vs, P v
      | chanstate.Closed buffer => False
      | _ => True
      end
  )%I.
#[global] Opaque is_chan_handoff.
#[local] Transparent is_chan_handoff.
#[global] Instance is_chan_handoff_pers γ ch P : Persistent (is_chan_handoff γ ch P).
Proof. apply _. Qed.

Lemma start_handoff (ch : loc) (γ : chan_names) (P : V → iProp Σ) :
  is_chan ch γ V -∗
  own_chan γ V chanstate.Idle ={⊤}=∗
  ∃ γhandoff,  ⌜γ = γhandoff.(chan_name)⌝ ∗ is_chan_handoff γhandoff ch P.
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

Lemma start_handoff_buffered (ch : loc) (γ : chan_names) (P : V → iProp Σ) :
  is_chan ch γ V -∗
  own_chan γ V (chanstate.Buffered []) ={⊤}=∗
  ∃ γhandoff,  ⌜γ = γhandoff.(chan_name)⌝ ∗  is_chan_handoff γhandoff ch P.
Proof.
  iIntros "#Hch Hoc".
  iExists {|
    chan_name := γ;
  |}.
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. simpl. done. }
  simpl.
  by iFrame "#".
Qed.

Lemma handoff_rcv_au γ ch P Φ  :
  is_chan_handoff γ ch P ⊢
  £1 ∗ £1  -∗
  (▷ ∀ v, P v -∗ Φ v true ) -∗
  recv_au γ.(chan_name) V Φ.
Proof.
  iIntros "#Hhandoff (Hlc1 & Hlc2 ) HΦ".
  iNamed "Hhandoff".
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

Lemma wp_handoff_receive γ ch P :
  {{{ is_chan_handoff γ ch P }}}
    chan.receive t #ch
  {{{ v, RET (#v, #true); P v }}}.
Proof using All.
  wp_start_folded as "#Hhandoff".
  iNamed "Hhandoff".
  wp_apply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (handoff_rcv_au with "[] [$Hlc1 $Hlc2]").
  {
    iFrame "#".
  }
  {
   iNext. iFrame.
  }
Qed.

Lemma handoff_send_au γ ch P v (Φ: iProp Σ) :
  is_chan_handoff γ ch P ∗ £1 ∗ £1 ⊢
  P v -∗
  (▷ Φ) -∗
  send_au γ.(chan_name) v Φ.
Proof.
  iIntros "(#Hhandoff & ? & ?) HP HΦ".
  iNamed "Hhandoff".
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

Lemma wp_handoff_send γ ch v P :
  {{{ is_chan_handoff γ ch P ∗ P v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof using All.
  wp_start_folded as "[#Hhandoff HP]".
  unfold is_chan_handoff. iNamed "Hhandoff".
  wp_apply (chan.wp_send ch with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & ? & ?)".
  iApply (handoff_send_au with "[$] [$HP]").
  iNext. by iApply "HΦ".
Qed.

End proof.
