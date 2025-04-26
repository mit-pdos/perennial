Require Import New.proof.proof_prelude.

Section onetime_barrier.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.

Implicit Types (s : chanstate.t unit).

Record params :=
  {
    gauge_init : nat; (* XXX: putting "gauge" in the name because this would
                       change under a `chan` gauge transformation. *)
    send_gn : gname;
    recv_gn : gname;
  }.
Implicit Types γ : params.

Definition own_send_tok γ := ghost_var γ.(send_gn) 1 ().
Definition own_recv_tok γ := ghost_var γ.(recv_gn) 1 ().

Definition is_onetime_barrier γ (ch : chan.t) Sd Rv : iProp Σ :=
  is_chan () ch ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_chan ch s ∗
        "%Hcap" ∷ ⌜ s.(chanstate.cap) = W64 0 ⌝ ∗
        "%Hopen" ∷ ⌜ s.(chanstate.closed) = false ⌝ ∗
        "%Hoffset_r" ∷ ⌜ γ.(gauge_init) ≤ s.(chanstate.received) ⌝%nat ∗
        "%Hoffset_s" ∷ ⌜ γ.(gauge_init) ≤ length s.(chanstate.sent) ⌝%nat ∗
        "Hr" ∷ match (s.(chanstate.received) - γ.(gauge_init))%nat with
          | O => True
          | S _ => (Rv ∨ own_send_tok γ)
          end ∗
        "Hs" ∷ match (length s.(chanstate.sent) - γ.(gauge_init))%nat with
          | O => True
          | S _ => (Sd ∨ own_recv_tok γ)
          end
    ).

Lemma start_onetime_barrier Sd Rv ch s:
  s.(chanstate.cap) = (W64 0) →
  s.(chanstate.closed) = false →
  s.(chanstate.received) = length s.(chanstate.sent) →
  is_chan () ch -∗
  own_chan ch s ={⊤}=∗
  ∃ γ, is_onetime_barrier γ ch Sd Rv ∗
       own_recv_tok γ ∗
       own_send_tok γ.
Proof.
  intros.
  iIntros "#? Hchan".
  iMod (ghost_var_alloc ()) as "[% ?]".
  iMod (ghost_var_alloc ()) as "[% ?]".
  iExists _.
  instantiate (1:=(ltac:(econstructor))). simpl.
  iFrame "#". iFrame. simpl.
  iApply inv_alloc.
  iNext. iFrame "∗%".
  instantiate (1:=s.(chanstate.received)).
  iSplitR; first word.
  iSplitR; first word.
  rewrite H1 Nat.sub_diag //.
Qed.

Lemma wp_onetime_barrier_receive γ ch Sd Rv :
  {{{
      is_onetime_barrier γ ch Sd Rv ∗
      own_recv_tok γ ∗
      Rv
  }}}
    chan.receive #ch
  {{{
      RET (#(), #true); Sd
  }}}.
Proof.
  iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
  wp_apply (wp_chan_receive (V:=()) with "[$]").

  (* send Rv *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  rewrite Hopen.
  iIntros "Hch".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-Htok HΦ]").
  { iNext. iFrame "∗%".
    simpl. iSplitR; first word.
    rewrite Nat.sub_succ_l //. iFrame.
  }
  iModIntro.

  (* get Sd *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  iIntros "* % Hch".

  edestruct (length _ - _)%nat eqn:?.
  { simpl in *. exfalso. apply lookup_lt_Some in H. lia. }
  iDestruct "Hs" as "[Hs|Hbad]".
  2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-HΦ Hs]").
  { iNext. iFrame "∗%". destruct (_ - _)%nat; iFrame. }
  iModIntro.
  destruct v.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_onetime_barrier_send γ ch Sd Rv :
  {{{
      is_onetime_barrier γ ch Sd Rv ∗
      own_send_tok γ ∗
      Sd
  }}}
    chan.send #ch #()
  {{{
      RET #(); Rv
  }}}.
Proof.
  iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
  wp_apply (wp_chan_send (V:=()) with "[$]").

  (* send Sd *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame "∗%".
  iIntros "Hch".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-Htok HΦ]").
  { iNext. iFrame "∗%". iSplitR.
    { rewrite length_app /=. iPureIntro. lia. }
    iClear "Hs". by destruct Nat.sub; iFrame.
  }
  iModIntro.

  (* get Rv *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  iIntros "* % Hch".

  edestruct (chanstate.received s0 - _)%nat eqn:?.
  { simpl in *. exfalso. word. }
  iDestruct "Hr" as "[Hr|Hbad]".
  2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-HΦ Hr]").
  { iNext. iFrame "∗%". by destruct Nat.sub; iFrame. }
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End onetime_barrier.
