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

Definition own_closeable_chan ch Pclose : iProp Σ :=
  ∃ γch, is_closeable_chan_internal ch γch Pclose ∗
         own γch.(closed_gn) (to_dfrac_agree (DfracOwn (1/2)) false).
#[global] Opaque own_closeable_chan.
#[local] Transparent own_closeable_chan.

(* Note: could make the namespace be user-chosen *)
Definition is_closeable_chan (ch : chan.t) (Pclose : iProp Σ) : iProp Σ :=
  ∃ γch, is_closeable_chan_internal ch γch Pclose.
#[global] Opaque is_closeable_chan.
#[local] Transparent is_closeable_chan.
#[global] Instance is_closeable_chan_pers ch P :
  Persistent (is_closeable_chan ch P) := _.

Definition is_closed_chan (ch : chan.t) (Pclose : iProp Σ) : iProp Σ :=
  ∃ γch, is_closeable_chan_internal ch γch Pclose ∗
         own γch.(closed_gn) (to_dfrac_agree DfracDiscarded true).
#[global] Opaque is_closed_chan.
#[local] Transparent is_closed_chan.
#[global] Instance is_closed_chan_pers ch P :
  Persistent (is_closed_chan ch P) := _.

Lemma closeable_chan_receive ch Pclosed Φ :
  is_closeable_chan ch Pclosed -∗
  (Pclosed ∗ is_closed_chan ch Pclosed -∗ Φ (#(), #false)%V) -∗ receive_atomic_update unit ch Φ.
Proof.
  iNamed 1. iIntros "HΦ". rewrite /receive_atomic_update. iFrame "#".
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

Lemma own_closeable_chan_nonblocking_receive ch Pclosed Φ Φnotready :
  own_closeable_chan ch Pclosed -∗
  Φnotready -∗ nonblocking_receive_atomic_update unit ch Φ Φnotready.
Proof.
  iIntros "(% & H & Hown)". iNamed "H". iIntros "HΦ". rewrite /nonblocking_receive_atomic_update. iFrame "#".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct decide as [|].
  - destruct a as [-> ?]. iRight in "Hclosed". iCombine "Hown Hclosed" gives %Hbad.
    exfalso. rewrite dfrac_agree_op_valid in Hbad. naive_solver.
  - destruct lookup eqn:Hlookup.
    { simpl. apply lookup_lt_Some in Hlookup. word. }
    iFrame.
    iIntros "Hch". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-]"). { iFrame "∗#%". }
    done.
Qed.

Lemma is_closed_chan_nonblocking_receive ch Pclosed Φ Φnotready :
  is_closed_chan ch Pclosed -∗
  Φ (#(), #false)%V -∗ nonblocking_receive_atomic_update unit ch Φ Φnotready.
Proof.
  iIntros "(% & H & #His)". iNamed "H". iIntros "HΦ". rewrite /nonblocking_receive_atomic_update. iFrame "#".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct decide as [|].
  - destruct st. destruct a as [? ?]. subst. simpl in *. iIntros "Hch".
    iFrame. iMod "Hmask". iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
  - destruct st. simpl in *. destruct closed; first lia.
    iCombine "His Hopen" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
Qed.

Lemma wp_closeable_chan_close ch Pclosed Φ :
  own_closeable_chan ch Pclosed ∗ □ Pclosed -∗
  Φ #() -∗
  WP chan.close #ch {{ Φ }}.
Proof.
  iIntros "(Hown & #HP) HΦ". iDestruct "Hown" as (?) "(His & Hown)". iNamed "His".
  unshelve wp_apply (wp_chan_close with "[$]"); try tc_solve.
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct (st.(chanstate.closed)).
  { iRight in "Hclosed". iCombine "Hown Hclosed" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver. }
  iSplitR; first done. iIntros "Hch". iMod "Hmask" as "_".
  iCombine "Hown Hopen" as "Hown". rewrite -dfrac_agree_op dfrac_op_own Qp.half_half.
  iMod (own_update _ _ (to_dfrac_agree DfracDiscarded true) with "Hown") as "#H".
  { apply cmra_update_exclusive. done. }
  iMod ("Hclose" with "[-]"); last done.
  iFrame "∗#%".
Qed.

Lemma alloc_closeable_chan {E} Pclose ch (s : chanstate.t unit) :
  s.(chanstate.received) = length s.(chanstate.sent) →
  s.(chanstate.closed) = false →
  own_chan ch s ={E}=∗
  is_closeable_chan ch Pclose ∗
  own_closeable_chan ch Pclose.
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

End proof.
