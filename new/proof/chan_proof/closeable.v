From iris.algebra.lib Require Import dfrac_agree.
Require Import New.golang.theory.
Require Import New.proof.proof_prelude.

(** A pattern for channel usage: a channel that never has anything sent, and is
    only closed at some point. Closing transfers a persistent proposition to
    readers. *)

Record closeable_internal_names :=
  { closed_gn : gname }.

Module closeable.
Inductive t := Open | Closed | Unknown.
End closeable.
Import closeable.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!go.Semantics}.

(* Note: could make the namespace be user-chosen *)
#[local] Definition is_closeable_chan_internal (ch : chan.t) γ γch (Pclose : iProp Σ) : iProp Σ :=
  "#His_ch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ (st : chanstate.t unit),
        "Hch" ∷ own_chan γ unit st ∗
        "Hs" ∷ (match st with
                | chanstate.Idle
                | chanstate.RcvPending =>
                    own γch.(closed_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
                | chanstate.Closed [] =>
                    □ Pclose ∗ own γch.(closed_gn) (to_dfrac_agree DfracDiscarded true)
                | _ => False
                end)
    ).

Definition own_closeable_chan (ch : chan.t) γ (Pclose : iProp Σ) (closed : closeable.t) : iProp Σ :=
  ∃ γch,
  "#Hinv" ∷ is_closeable_chan_internal ch γ γch Pclose ∗
  "Hown" ∷ (match closed with
            | Open => own γch.(closed_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
            | Closed => own γch.(closed_gn) (to_dfrac_agree DfracDiscarded true)
            | Unknown => True
            end).

#[global] Opaque own_closeable_chan.
#[local] Transparent own_closeable_chan.
#[global] Instance own_closeable_chan_Unknown_pers ch γch P :
  Persistent (own_closeable_chan ch γch P Unknown) := _.
#[global] Instance own_closeable_chan_Closed_pers ch γch P :
  Persistent (own_closeable_chan ch γch P Closed) := _.

Lemma closeable_chan_closed ch γ Pclose :
  £ 1 -∗ own_closeable_chan ch γ Pclose Closed ={⊤}=∗
  Pclose.
Proof.
  iIntros "Hlc". iNamed 1. iNamed "Hinv". iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  destruct st; try by iExFalso; simpl.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - destruct drain; try done.
    iClear "Hown". iDestruct "Hs" as "[#? ?]". iMod ("Hclose" with "[-]"). { iFrame. iFrame "∗#". }
    iModIntro. iFrame "#".
Qed.

Lemma closeable_chan_receive ch γ Pclosed Φ cl :
  own_closeable_chan ch γ Pclosed cl -∗
  (Pclosed ∗ own_closeable_chan ch γ Pclosed Closed -∗ Φ () false) -∗
  recv_au γ unit Φ.
Proof.
  iNamed 1. iIntros "HΦ".  iNamed "Hinv".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct st; try done.
  - iIntros "Hch". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#%". }
    iModIntro.
    iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
    iNext. iNamed "Hi". iFrame. destruct st; try done.
    destruct drain; try done. iIntros "Hch". iDestruct "Hs" as "[#? #?]".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#". }
    iApply "HΦ". iModIntro. iFrame "∗#".
  - destruct drain; try done. iIntros "Hch".
    iDestruct "Hs" as "[#? #?]". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#%". }
    iApply "HΦ". iModIntro. iFrame "∗#".
Qed.

Lemma own_closeable_chan_nonblocking_receive ch γ Pclosed Φ Φnotready cl :
  own_closeable_chan ch γ Pclosed cl -∗
  (match cl with
   | Unknown | Closed => (own_closeable_chan ch γ Pclosed Closed -∗ Φ () false)
   | _ => True
   end ∧
   match cl with
   | Unknown | Open => (own_closeable_chan ch γ Pclosed cl -∗ Φnotready)
   | _ => True
   end)
  -∗
  nonblocking_recv_au_alt γ unit Φ Φnotready.
Proof.
  iNamed 1. iNamed "Hinv". subst.
  iIntros "HΦ".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct st; try done.
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
  - destruct drain; try done. iDestruct "Hs" as "[#? #Hs]". destruct cl.
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iDestruct ("HΦ" with "[$]") as "$". iIntros "Hch".
      iMod "Hmask" as "_". iMod ("Hclose" with "[-]"); last done. iFrame "∗#".
    + iLeft in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iIntros "Hch".
      iMod "Hmask" as "_". iMod ("Hclose" with "[-]"); last done. iFrame "∗#".
Qed.

Lemma wp_closeable_chan_close `[!ty ↓u go.ChannelType dir (go.StructType [])] ch γch Pclosed :
  {{{ own_closeable_chan ch γch Pclosed Open ∗ □ Pclosed }}}
  #(functions go.close [ty]) #ch
  {{{ RET #(); own_closeable_chan ch γch Pclosed Closed }}}.
Proof.
  wp_start_folded as "[Hown #?]". iNamed "Hown". iNamed "Hinv".
  wp_apply (chan.wp_close with "[$]"). iIntros "Hlcs".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct st; try done.
  - iIntros "Hch". iMod "Hmask" as "_".
    iCombine "Hown Hs" as "Hown". rewrite -dfrac_agree_op dfrac_op_own Qp.half_half.
    iMod (own_update  _ _ (to_dfrac_agree DfracDiscarded true) with "Hown") as "#H".
    { apply cmra_update_exclusive. done. }
    iSpecialize ("HΦ" with "[$]"). iFrame.
    iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
  - destruct drain; try done. iRight in "Hs".
    iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
Qed.

Lemma alloc_closeable_chan {E} Pclose γ ch :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={E}=∗
  own_closeable_chan ch γ Pclose Open.
Proof.
  iIntros "#? Hch".
  iMod (own_alloc
          ((to_dfrac_agree (DfracOwn (1/2)) false) ⋅ (to_dfrac_agree (DfracOwn (1/2)) false))
       ) as (tok_gn) "Htok".
  { rewrite -dfrac_agree_op //. }
  iDestruct "Htok" as "[Htok Htok2]".
  iAssert (|={E}=> is_closeable_chan_internal ch γ ltac:(econstructor) Pclose)%I with "[-Htok]" as ">#H".
  2:{ iFrame "∗#". simpl. iFrame. done. }
  simpl. iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame. iFrame.
Qed.

Lemma own_closeable_chan_Unknown ch γ Pclose cl :
  own_closeable_chan ch γ Pclose cl -∗
  own_closeable_chan ch γ Pclose Unknown.
Proof. iNamed 1. iFrame "#". Qed.

End proof.
