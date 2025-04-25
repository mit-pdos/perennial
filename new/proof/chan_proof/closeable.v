Require Import New.proof.proof_prelude.

(** A pattern for channel usage: a channel that never has anything sent, and is
    only closed at some point. Closing transfers a persistent proposition to
    readers. *)
Class closeable_chanG Σ :=
  {
    ghost_varG :: ghost_varG Σ ()
  }.

Record closeable_chan_names :=
  {
    tok_gn : gname;
    init_len : nat; (* for gauge invariance *)
  }.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{closeable_chanG Σ}.

Local Definition own_closeable_chan γch : iProp Σ :=
  ghost_var γch.(tok_gn) 1 ().

(* Note: could make the namespace be user-chosen *)
Definition is_closeable_chan V `{!IntoVal V} (ch : chan.t) γch (Pclose : iProp Σ) : iProp Σ :=
  "#His_ch" ∷ is_chan V ch ∗
  "#Hinv" ∷ inv nroot (
      ∃ (st : chanstate.t V),
        "ch" ∷ own_chan ch st ∗
        "%Hempty" ∷ ⌜ length st.(chanstate.sent) = γch.(init_len) ⌝ ∗
        "%Hle" ∷ ⌜ length st.(chanstate.sent) ≤ st.(chanstate.received) ⌝ ∗
        "#HPclosed" ∷ (if st.(chanstate.closed) then (□ Pclose) else True) ∗
        "Hclosed" ∷ (if st.(chanstate.closed) then own_closeable_chan γch else True)
    ).
#[global] Opaque is_closeable_chan.
#[local] Transparent is_closeable_chan.
#[global] Instance is_closeable_chan_pers V `{!IntoVal V} γch ch P :
  Persistent (is_closeable_chan V γch ch P) := _.

Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Lemma closeable_chan_receive ch γch Pclosed Φ :
  is_closeable_chan V ch γch Pclosed -∗
  (Pclosed -∗ Φ (#(default_val V), #false)%V) -∗ receive_atomic_update ch Φ (V:=V).
Proof.
  iNamed 1. iIntros "HΦ". rewrite /receive_atomic_update.
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct decide as [|].
  - iIntros "Hch". iFrame.
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ]").
    { iFrame "∗#%". } iApply "HΦ". destruct st.(chanstate.closed); try done.
    naive_solver.
  - (* eventually get a contradiction down this path *)
    iIntros "Hch". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-]"). { iFrame "∗#%". iPureIntro. simpl. lia. }
    iModIntro.
    iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
    iNext. iNamed "Hi". iFrame. iIntros (?) "%Hbad".
    exfalso. apply lookup_lt_Some in Hbad. lia.
Qed.

Lemma wp_closeable_chan_close ch γch Pclosed Φ :
  is_closeable_chan V ch γch Pclosed ∗ own_closeable_chan γch ∗ □ Pclosed -∗
  Φ #() -∗
  WP chan.close #ch {{ Φ }}.
Proof.
  iIntros "(#His & Hown & #HP) HΦ". iNamed "His".
  unshelve wp_apply (wp_chan_close with "[$]"); try tc_solve.
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct (st.(chanstate.closed)).
  { iCombine "Hown Hclosed" gives %Hbad. exfalso. naive_solver. }
  iSplitR; first done. iIntros "Hch". iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); last done.
  iFrame "∗#%".
Qed.

Lemma alloc_closeable_chan {E} Pclose ch (s : chanstate.t V) :
  s.(chanstate.received) = length s.(chanstate.sent) →
  s.(chanstate.closed) = false →
  is_chan V ch -∗
  own_chan ch s ={E}=∗
  ∃ γch,
  is_closeable_chan V ch γch Pclose ∗
  own_closeable_chan γch.
Proof.
  intros ? Hnotclosed. iIntros "His Hch".
  iMod (ghost_var_alloc ()) as (tok_gn) "Htok".
  iExists _. instantiate (1:=ltac:(econstructor)).
  simpl. iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame. rewrite Hnotclosed. simpl.
  iPureIntro. split; [done|lia].
Qed.

End proof.
