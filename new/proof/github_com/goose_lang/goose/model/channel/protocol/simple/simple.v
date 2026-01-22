Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import
  chan_au_base.
Require Import New.golang.theory.

(** * Simple Channel Pattern Verification

    This file provides verification for the "simple" pattern - a channel with a
    predicate P over values sent on the channel.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!chanG Σ V].
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t] `[!go.TypeRepr t V].

Record simple_names := {
  chan_name : chan_names;
}.

(* TODO: should not have to be exposed *)
Definition is_simple (γ : simple_names) (ch : loc) (P : V → iProp Σ) : iProp Σ :=
  "#Hch" ∷ is_channel ch γ.(chan_name) ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chan_rep.t V),
      "Hch" ∷ own_channel ch s γ.(chan_name) ∗
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
#[global] Instance is_simple_pers γ ch P : Persistent (is_simple γ ch P).
Proof. apply _. Qed.

Lemma start_simple (ch : loc) (γ : chan_names) (P : V → iProp Σ) :
  is_channel ch γ -∗
  own_channel ch chan_rep.Idle γ ={⊤}=∗
  ∃ γsimple,  ⌜γ = γsimple.(chan_name)⌝ ∗ is_simple γsimple ch P.
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

Lemma start_simple_buffered (ch : loc) (γ : chan_names) (P : V → iProp Σ) :
  is_channel ch γ -∗
  own_channel ch (chan_rep.Buffered []) γ ={⊤}=∗
  ∃ γsimple,  ⌜γ = γsimple.(chan_name)⌝ ∗  is_simple γsimple ch P.
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

Local Set Default Proof Using "All".

Lemma simple_rcv_au γ ch P Φ  :
  is_simple γ ch P ⊢
  £1 ∗ £1  -∗
  (▷ ∀ v, P v -∗ Φ v true ) -∗
  rcv_au_slow ch γ.(chan_name) Φ.
Proof.
  iIntros "#Hsimple (Hlc1 & Hlc2 ) HΦ".
  iNamed "Hsimple".
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

Lemma wp_simple_receive γ ch P :
  {{{ is_simple γ ch P }}}
    chan.receive t #ch
  {{{ v, RET (#v, #true); P v }}}.
Proof.
  wp_start_folded as "#Hsimple".
  iNamed "Hsimple".
  wp_apply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (simple_rcv_au with "[] [$Hlc1 $Hlc2]").
  {
    iFrame "#".
  }
  {
   iNext. iFrame.
  }
Qed.

Lemma simple_send_au γ ch P v (Φ: iProp Σ) :
  is_simple γ ch P ∗ £1 ∗ £1 ⊢
  P v -∗
  (▷ Φ) -∗
  send_au_slow ch v γ.(chan_name) Φ.
Proof.
  iIntros "(#Hsimple & ? & ?) HP HΦ".
  iNamed "Hsimple".
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
    unfold send_au_inner.
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

Lemma wp_simple_send γ ch v P :
  {{{ is_simple γ ch P ∗
      P v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "[#Hsimple HP]".
  unfold is_simple. iNamed "Hsimple".
  wp_apply (chan.wp_send ch with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & ? & ?)".
  iApply (simple_send_au with "[$] [$HP]").
  iNext. by iApply "HΦ".
Qed.

End proof.
