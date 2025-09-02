Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_send chan_au_recv chan_au_base chan_init.

Section handshake.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.
Context `{!chanGhostStateG Σ ()}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Implicit Types (s : chan_rep.t ()).

Record params :=
  {
    chan_gn : chan_names;
  }.


Definition is_handshake γ (ch : loc) P Q : iProp Σ :=
  is_channel ch 0 γ.(chan_gn)  ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_channel ch s 0 γ.(chan_gn) ∗
    (match s with
     | chan_rep.Idle =>
        True
     | chan_rep.SndWait _ | chan_rep.SndDone _ =>
         P
     | chan_rep.RcvWait | chan_rep.RcvDone =>
         Q
     (* Can't use buffered channel and we don't close here. *)
     | _ => False
     end
    )).

Lemma start_handshake P Q ch s γ:
  is_channel ch 0 γ.(chan_gn)  -∗
  own_channel ch chan_rep.Idle 0 γ.(chan_gn) ={⊤}=∗
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
         £ 1 ∗  £ 1 ∗  £ 1 ∗
      is_pkg_init channel ∗
      is_handshake γ ch P Q  ∗
      Q
  }}}
    ch @ (ptrT.id channel.Channel.id) @ "Receive" #(structT []) #()
  {{{
      RET (#(), #true); P
  }}}.
Proof.
  iIntros (?) "(Hlc1 & Hlc2 & Hlc3 & Hpc & (#Hchan & #Hinv) & HQ) HΦ".
  iApply ((wp_Receive ch 0  γ.(chan_gn) Φ  ) with "[$Hpc $Hchan]").
  iModIntro. unfold chan_blocking_receive_atomic_update.
  iFrame "#".
  iInv "Hinv" as "Hi" "Hclose".
   iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".
   iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
   destruct s. all:try done.
   -   iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ Hlc2]").
    +  iModIntro. iExists chan_rep.RcvWait.  iFrame.
    + iModIntro.  iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".  iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
   iModIntro. iExists s. iFrame. destruct s. all: try done.
   { iMod "Hmask" as "_". iIntros "Hid". iMod ("Hclose" with "[-HΦ Hi]").
     { iModIntro.  iFrame. }
     iModIntro. replace v with (). { iApply "HΦ". done. }
     destruct v.
      done.
   }
   -  iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ Hlc2 Hi]").
    + iModIntro. iFrame.
    + iModIntro. destruct v. iApply "HΦ". done.
Qed.

Lemma wp_handshake_send γ ch P Q :
  {{{
         £ 1 ∗  £ 1 ∗  £ 1 ∗
      is_pkg_init channel ∗
      is_handshake γ ch P Q ∗
      P
  }}}
    ch @ (ptrT.id channel.Channel.id) @ "Send" #(structT []) #()
  {{{
      RET (#()); Q
  }}}.
Proof.
  iIntros (?) "(Hlc1 & Hlc2 & Hlc3 & Hpc & (#Hchan & #Hinv) & HP) HΦ".
  iApply ((wp_Send ch 0 ()  γ.(chan_gn) Φ  ) with "[$Hpc $Hchan]").
  iModIntro. unfold chan_blocking_receive_atomic_update.
  iFrame "#".
  iInv "Hinv" as "Hi" "Hclose".
   iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".
   iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
   destruct s. all:try done.
   -   iIntros "H".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ Hlc2]").
    +  iModIntro. iExists (chan_rep.SndWait ()).  iFrame.
    + iModIntro.  iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
   iNamed "Hi".  iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
   iModIntro. iExists s. iFrame. destruct s. all: try done.
   { iMod "Hmask" as "_". iIntros "Hid". iMod ("Hclose" with "[-HΦ Hi]").
     { iModIntro.  iFrame. }
     iModIntro.  iApply "HΦ". done.
   }
   - iIntros "Hsd".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ Hlc2 Hi]").
    + iModIntro.  iFrame.
    + iModIntro.  iApply "HΦ". done.
Qed.

End handshake.
