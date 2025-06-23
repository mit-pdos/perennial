From iris.algebra.lib Require Import dfrac_agree.
Require Import New.proof.proof_prelude.

(** A pattern for channel usage: a channel that never has anything sent, and is
    only closed at some point. Closing transfers a persistent proposition to
    readers. *)
Class closeable_chanG Σ :=
  {
    close_tok_inG :: inG Σ (dfrac_agreeR boolO)
  }.

Record closeable_chan_names :=
  {
    closed_gn : gname;
    init_len : nat; (* for gauge invariance *)
  }.

Module closeable.
Inductive t :=
| Open
| Closed
| Unknown.
End closeable.
Import closeable.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!closeable_chanG Σ}.

(* Note: could make the namespace be user-chosen *)
Local Definition is_closeable_chan_internal (ch : chan.t) γch (Pclose : iProp Σ) : iProp Σ :=
  "#His_ch" ∷ is_chan unit ch ∗
  "#Hinv" ∷ inv nroot (
      ∃ (st : chanstate.t unit),
        "ch" ∷ own_chan ch st ∗
        "%Hempty" ∷ ⌜ length st.(chanstate.sent) = γch.(init_len) ⌝ ∗
        "%Hle" ∷ ⌜ length st.(chanstate.sent) ≤ st.(chanstate.received) ⌝ ∗
        "#Hclosed" ∷ (if st.(chanstate.closed) then
                        (□ Pclose ∗ own γch.(closed_gn) (to_dfrac_agree DfracDiscarded true))
                     else True) ∗
        "Hopen" ∷ (if st.(chanstate.closed) then True
                   else own γch.(closed_gn) (to_dfrac_agree (DfracOwn (1/2)) false))
    ).

Definition own_closeable_chan (ch : chan.t) (Pclose : iProp Σ) (closed : closeable.t) : iProp Σ :=
  ∃ γch,
    "#Hinv" ∷ is_closeable_chan_internal ch γch Pclose ∗
    "Hown" ∷ (match closed with
              | Open => own γch.(closed_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
              | Closed => own γch.(closed_gn) (to_dfrac_agree DfracDiscarded true)
              | Unknown => True
              end).

#[global] Opaque own_closeable_chan.
#[local] Transparent own_closeable_chan.
#[global] Instance own_closeable_chan_Unknown_pers ch P :
  Persistent (own_closeable_chan ch P Unknown) := _.
#[global] Instance own_closeable_chan_Closed_pers ch P :
  Persistent (own_closeable_chan ch P Closed) := _.

Lemma closeable_chan_receive ch Pclosed Φ cl :
  own_closeable_chan ch Pclosed cl -∗
  (Pclosed ∗ own_closeable_chan ch Pclosed Closed -∗ Φ (#(), #false)%V) -∗
  receive_atomic_update unit ch Φ.
Proof.
  iNamed 1. iIntros "HΦ". rewrite /receive_atomic_update. iNamed "Hinv".
  iFrame "#".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct decide as [|].
  - iIntros "Hch". iFrame.
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ]").
    { iFrame "∗#%". } iApply "HΦ". destruct st.(chanstate.closed); last naive_solver.
    iDestruct "Hclosed" as "[#$ $]". iFrame "#". done.
  - (* eventually get a contradiction down this path *)
    iIntros "Hch". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-]"). { iFrame "∗#%". iPureIntro. simpl. lia. }
    iModIntro.
    iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
    iNext. iNamed "Hi". iFrame. iIntros (?) "%Hbad".
    exfalso. apply lookup_lt_Some in Hbad. lia.
Qed.

Lemma own_closeable_chan_nonblocking_receive ch Pclosed Φ Φnotready cl :
  own_closeable_chan ch Pclosed cl -∗
  (match cl with
   | Unknown | Closed => (own_closeable_chan ch Pclosed Closed -∗ Φ (#(), #false)%V)
   | _ => True
   end ∧
   match cl with
   | Unknown | Open => (own_closeable_chan ch Pclosed cl -∗ Φnotready)
   | _ => True
   end)
  -∗
  nonblocking_receive_atomic_update unit ch Φ Φnotready.
Proof.
  iNamed 1. iNamed "Hinv".
  iIntros "HΦ". rewrite /nonblocking_receive_atomic_update. iFrame "#".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct st. simpl in *.
  destruct lookup eqn:Hlookup.
  { exfalso. apply lookup_lt_Some in Hlookup. lia. }
  destruct closed.
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iRight in "Hclosed". iCombine "Hclosed Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
    + iLeft in "HΦ". iDestruct "Hclosed" as "[? ?]".
      iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
    + iCombine "Hopen Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
Qed.

Lemma wp_closeable_chan_close ch Pclosed :
  {{{ own_closeable_chan ch Pclosed Open ∗ □ Pclosed }}}
  chan.close #ch
  {{{ RET #(); own_closeable_chan ch Pclosed Closed }}}.
Proof.
  wp_start as "[Hown #?]". iNamed "Hown". iNamed "Hinv".
  unshelve wp_apply (wp_chan_close with "[$]"); try tc_solve.
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct (st.(chanstate.closed)).
  { iRight in "Hclosed". iCombine "Hown Hclosed" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver. }
  iSplitR; first done. iIntros "Hch". iMod "Hmask" as "_".
  iCombine "Hown Hopen" as "Hown". rewrite -dfrac_agree_op dfrac_op_own Qp.half_half.
  iMod (own_update _ _ (to_dfrac_agree DfracDiscarded true) with "Hown") as "#H".
  { apply cmra_update_exclusive. done. }
  iSpecialize ("HΦ" with "[$]"). iFrame.
  iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
Qed.

Lemma alloc_closeable_chan {E} Pclose ch (s : chanstate.t unit) :
  s.(chanstate.received) = length s.(chanstate.sent) →
  s.(chanstate.closed) = false →
  own_chan ch s ={E}=∗
  own_closeable_chan ch Pclose Open.
Proof.
  intros ? Hnotclosed. iIntros "Hch". iDestruct (own_chan_is_chan with "Hch") as "#His".
  iMod (own_alloc
          ((to_dfrac_agree (DfracOwn (1/2)) false) ⋅ (to_dfrac_agree (DfracOwn (1/2)) false))
       ) as (tok_gn) "Htok".
  { rewrite -dfrac_agree_op //. }
  iDestruct "Htok" as "[Htok Htok2]".
  iAssert (|={E}=> is_closeable_chan_internal ch ltac:(econstructor) Pclose)%I with "[-Htok]" as ">#H".
  2:{ iFrame "∗#". simpl. iFrame. done. }
  simpl. iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame. rewrite Hnotclosed. iFrame. simpl.
  iPureIntro. split; [done|lia].
Qed.

Lemma own_closeable_chan_Unknown ch Pclose cl :
  own_closeable_chan ch Pclose cl -∗
  own_closeable_chan ch Pclose Unknown.
Proof. iNamed 1. iFrame "#". Qed.

End proof.
