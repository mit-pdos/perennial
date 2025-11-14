Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export protocol.base.
From New.golang.theory Require Import chan.

Section handshake.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!chan_protocolG Σ V}.

(*----------------------------------------------------------------------------
  Invariant for a simple handshake on an unbuffered channel with unit payloads.

  - When the channel has an in-flight *send* (SndWait/SndDone), predicate [P]
    must hold (producer-side obligation).
  - When the channel has an in-flight *receive* (RcvWait/RcvDone), predicate [Q]
    must hold (consumer-side obligation).
  - Buffered channels are intentionally disallowed.
  - Closing is also disallowed in this protocol ([_ => False]).

  ---------------------------------------------------------------------------*)
Definition is_handshake γ (ch : loc)  (P: V -> iProp Σ) Q : iProp Σ :=
  is_channel ch γ  ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_channel ch s γ ∗
    (match s with
     | chan_rep.Idle =>
        True
     | chan_rep.SndPending v | chan_rep.SndCommit v =>
         P v
     | chan_rep.RcvPending | chan_rep.RcvCommit =>
         Q
     (* Can't use buffered channel and we don't close here. *)
     | _ => False
     end
    )).

Lemma start_handshake ch P Q  γ:
  is_channel  ch γ  -∗
  own_channel  ch chan_rep.Idle γ ={⊤}=∗
  is_handshake γ ch P Q .
Proof.
    intros.
  iIntros "#? Hchan".
  iFrame "#". iFrame. simpl.
  iApply inv_alloc.
 iExists chan_rep.Idle.
 iFrame "∗%#".
Qed.

Lemma wp_handshake_receive γ ch P Q :
  {{{
      is_pkg_init channel ∗
      is_handshake γ ch P Q  ∗
      Q
  }}}
    chan.receive #t #ch
  {{{
      v, RET (#v, #true); P v
  }}}.
Proof.
  iIntros (?) "(Hpc & (#Hchan & #Hinv) & HQ) HΦ".
  wp_apply ((chan.wp_receive ch γ Φ  ) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".
   iMod (lc_fupd_elim_later with "[$] HΦ") as "Hau".
  iFrame "#".
  iInv "Hinv" as "Hi" "Hclose".
   iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".
   iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
   destruct s. all:try done.
   -   iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-Hau Hlc1]").
    +  iModIntro. iExists chan_rep.RcvPending.  iFrame.
    + iModIntro.  iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".  iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
   iModIntro. iExists s. iFrame. destruct s. all: try done.
   { iMod "Hmask" as "_". iIntros "Hid". iMod ("Hclose" with "[-Hau Hi]").
     { iModIntro.  iFrame. }
     iModIntro.  { iApply "Hau". done. }
   }
   -  iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-Hau Hlc1 Hi]").
    + iModIntro. iFrame.
    + iModIntro.
       iApply "Hau". done.
Qed.

Lemma wp_handshake_send γ ch v P Q :
  {{{
      is_pkg_init channel ∗
      is_handshake γ ch P Q ∗
      P v
  }}}
    chan.send #t #ch #v
  {{{
      RET (#()); Q
  }}}.
Proof.
  iIntros (?) "(Hpc & (#Hchan & #Hinv) & HP) HΦ".
  wp_apply ((chan.wp_send ch v γ Φ  ) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".
  iMod (lc_fupd_elim_later with "[$] HΦ") as "Hau".
  iFrame "#".
  iInv "Hinv" as "Hi" "Hclose".
   iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".
   iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
   destruct s. all:try done.
   -   iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-Hau Hlc1]").
    +  iModIntro. iExists (chan_rep.SndPending v).  iFrame.
    + iModIntro.  iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".  iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
   iModIntro. iExists s. iFrame. destruct s. all: try done.
   { iMod "Hmask" as "_". iIntros "Hid". iMod ("Hclose" with "[-Hau Hi]").
     { iModIntro.  iFrame. }
     iModIntro.  iApply "Hau". done.
   }
   - iIntros "Hsd".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-Hau Hlc1 Hi]").
    + iModIntro.  iFrame.
    + iModIntro.  iApply "Hau". done.
Qed.

End handshake.
