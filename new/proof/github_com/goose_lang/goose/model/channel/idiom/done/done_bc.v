Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.
From New.golang.theory Require Import chan.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import excl.

(** Done Channel For Persistent Broadcast

    This file provides a channel idiom spec where:
    - A single broadcaster closes the channel with a persistent resource Q
    - Any number of receivers can all receive and obtain Q
    
    Key features:
    - Broadcaster has exclusive close token and knows channel isn't already closed
    - On close: turn in token(right to close) + Q 
*)

Section done_bc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chan_idiomG Σ V}.
Context `{!inG Σ (exclR unitO)}.

Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.

Record done_bc_names := {
  bc_chan_name : chan_names;
  bc_saved_name : gname;
  bc_close_token_name : gname
}.

(** Broadcaster's exclusive token - allows closing once with Q *)
Definition Broadcast (γ : done_bc_names) (Q : iProp Σ) : iProp Σ :=
  own γ.(bc_close_token_name) (Excl ()) ∗
  saved_prop_own γ.(bc_saved_name) DfracDiscarded Q.

Definition is_done_bc (γ : done_bc_names) (ch : loc) (Q: iProp Σ) `{!Persistent Q} : iProp Σ :=
  is_chan ch γ.(bc_chan_name) ∗
  inv nroot (
    ∃ (s : chan_rep.t V),
      "Hch" ∷ own_chan ch s γ.(bc_chan_name) ∗
      "Hsaved" ∷ saved_prop_own γ.(bc_saved_name) DfracDiscarded Q ∗
      match s with
      | chan_rep.Idle | chan_rep.RcvPending => 
          True
      | chan_rep.Closed [] => 
         (* Take the own fact from the closer so they can get a contradiction
            until the channel is closed *)
          "HQ" ∷ Q  ∗ own γ.(bc_close_token_name) (Excl ())  
      | _ => False
      end
  )%I.

Lemma start_done_bc (ch : loc) (γ : chan_names) (Q : iProp Σ) `{!Persistent Q} :
  is_chan ch γ -∗
  own_chan ch chan_rep.Idle γ ={⊤}=∗
  ∃ γbc, is_done_bc γbc ch Q ∗ Broadcast γbc Q.
Proof.
  iIntros "#Hch Hoc".
  iMod (saved_prop_alloc Q DfracDiscarded) as (γsaved) "#Hsaved"; first done.
  iMod (own_alloc (Excl ())) as (γtoken) "Htoken"; first done.
  
  set (γbc := {|
    bc_chan_name := γ;
    bc_saved_name := γsaved;
    bc_close_token_name := γtoken
  |}).
  
  iMod (inv_alloc nroot _ (
    ∃ s,
      "Hch" ∷ own_chan ch s γ ∗
      "Hsaved" ∷ saved_prop_own γsaved DfracDiscarded Q ∗
       match s with
      | chan_rep.Idle | chan_rep.RcvPending => 
          True
      | chan_rep.Closed [] => 
          "HQ" ∷ Q ∗ own γtoken (Excl ())  
      | _ => False
      end
  )%I with "[Hoc]") as "#Hinv".
  {
    iNext. iExists chan_rep.Idle. iFrame "Hoc". iFrame "#%".
  }
  
  iModIntro. iExists γbc. iFrame "#".
  done.
Qed.

Lemma is_done_bc_is_chan γ ch Q `{!Persistent Q}:
  is_done_bc γ ch Q ⊢ is_chan ch γ.(bc_chan_name).
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma done_bc_close_au γ ch Q Φ `{!Persistent Q} :
  is_done_bc γ ch Q -∗
  Broadcast γ Q ∗ Q -∗
  ▷ Φ -∗
  close_au ch γ.(bc_chan_name) Φ.
Proof.
  iIntros "#Hbc  [[Htoken #HsavedB] HQ] HΦ".
  rewrite /is_done_bc. iDestruct "Hbc" as "[#Hisch #Hinv]".
  
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iNamed "Hinv_open".
  
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].

  iNext. iFrame "#". iFrame.
  iNamed "Hinv_open". iFrame.
  
  destruct s; try done.
  - iIntros "Hoc".
    iMod "Hmask".
    
    iDestruct (saved_prop_agree with "HsavedB Hsaved") as "#HQeq".
    
    iMod ("Hinv_close" with "[Hoc Hsaved HQ Htoken]") as "_".
    {
      iNext. iExists (chan_rep.Closed []).
      iFrame "%". iFrame.
    }
    iModIntro. iApply "HΦ".
    
  - destruct drain.
  {
    iDestruct "HQ" as "HQ;".
    iNamed "Hinv_open".
iCombine "Htoken Hinv_open" as "Hbad".
iDestruct (own_valid with "Hbad") as %Hvalid.
done.
  }
  done.
  

Qed.

Lemma wp_done_bc_close γ ch Q `{!Persistent Q} :
  {{{ is_done_bc γ ch Q ∗
      Broadcast γ Q ∗ Q }}}
    chan.close #t #ch
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hbc & HBcast & HQ) HΦ".
  iApply (chan.wp_close ch γ.(bc_chan_name) with "[#]").
  { iDestruct "Hbc" as "[$ _]". }
  iIntros "(Hlc & Hlcrest)".
  iApply (done_bc_close_au with "[] [$HBcast $HQ] [HΦ]").
  { iFrame "#". }
  iNext. iApply "HΦ". done.
Qed.

Lemma done_bc_receive_au γ ch Q `{!Persistent Q} :
  ∀ (Φ: V → bool → iProp Σ),
  is_done_bc γ ch Q -∗
  ▷ (Q -∗ Φ (default_val V) false) -∗
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  recv_au ch γ.(bc_chan_name) (λ (v:V) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hbc  HΦQ (Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  rewrite /is_done_bc. iDestruct "Hbc" as "[#Hisch #Hinv]".
  
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNamed "Hinv_open".
    iNext. iFrame "#".
    iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc Hsaved]") as "_".
    { iNext. iFrame. }
    iModIntro.
    
    rewrite /recv_nested_au.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    destruct s. all: try done.
    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"];
      iNext; iFrame "Hch".
    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"];
      iNext; iFrame "Hch".

    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"];
      iNext; iFrame "Hch".
      destruct drain; last done.
      iIntros "Hoc".
      iMod "Hmask2".
      iNamed "Hinv_open2".
      iDestruct "HQ" as "#HQ".
       iMod ("Hinv_close2" with "[Hoc Hsaved Hinv_open2]") as "_".
    { iNext. iFrame. iFrame "#%". done. }
    iModIntro.

      iApply "HΦQ". done.
  }
  {
    iFrame "Hch".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    done.

  }
  {
    destruct drain; last done.
    iFrame "Hch".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    iIntros "Hoc".
    iMod "Hmask".
    iNamed "Hinv_open".
    iDestruct "HQ" as "#HQ".
    iMod ("Hinv_close" with "[Hoc Hsaved HQ Hinv_open]") as "_".
    {
      iNext. iFrame. iFrame "#%". done.
    }
    iModIntro.
    iApply "HΦQ".
    done.
  }
Qed.

Lemma wp_done_bc_receive γ ch Q `{!Persistent Q} :
  {{{ is_done_bc γ ch Q }}}
    chan.receive #t #ch
  {{{ RET (#(default_val V), #false); Q }}}.
Proof.
  iIntros (Φ) "(#Hbc & #HWait) HΦ".
  iApply (chan.wp_receive ch γ.(bc_chan_name) with "[#]").
  { done. }
  iIntros "Hlc".
  iApply (done_bc_receive_au with "[][HΦ]").
  { iFrame "#". }
  { iNext. iIntros "HQ". iApply "HΦ". iFrame. }
  done.
  Unshelve.
  done.
Qed.

End done_bc.