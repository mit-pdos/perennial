From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import GenHeap.

From Perennial.Helpers Require Import Transitions.
Existing Instance r_mbind.


Section ghost_var_helpers.
Context {A: ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

Lemma ghost_var_alloc (a: A) :
  (|==> ∃ γ, own γ (● (Excl' a)) ∗ own γ (◯ (Excl' a)))%I.
Proof using H0.
  iMod (own_alloc (● (Excl' a) ⋅ ◯ (Excl' a))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists γ. iFrame.
Qed.

Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof using H H0.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Lemma ghost_var_update γ (a1' a1 a2 : A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) ==∗
    own γ (● (Excl' a1')) ∗ own γ (◯ (Excl' a1')).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' a1' ⋅ ◯ Excl' a1') with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

End ghost_var_helpers.



Definition LogSz := 511.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
         start: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; start>.
  Definition diskEnd (s:t): Z :=
    int.val s.(start) + Z.of_nat (length s.(upds)).
  Definition empty (s:t): t :=
    mk [] (diskEnd s).
End circΣ.

Notation start := circΣ.start.
Notation upds := circΣ.upds.

Definition circ_read : transition circΣ.t (list update.t * u64) :=
  s ← reads (fun x => (upds x, start x));
  ret s.

Definition assert `(P : T -> Prop) : transition T unit :=
  @suchThat _ unit (fun σ _ => P σ) (fallback_genPred _).

Definition circ_advance (newStart : u64) : transition circΣ.t unit :=
  assert (fun σ => int.val σ.(start) <= int.val newStart <= int.val σ.(start) + length σ.(upds));;
  modify (fun σ => set upds (skipn (Z.to_nat (int.val newStart - int.val σ.(start))%Z)) σ);;
  modify (set start (fun _ => newStart)).

Definition circ_append (l : list update.t) (endpos : u64) : transition circΣ.t unit :=
  assert (fun σ => int.val σ.(start) + length σ.(upds) = int.val endpos);;
  modify (set circΣ.upds (fun u => u ++ l));;
  assert (fun σ => length σ.(upds) <= LogSz).

Canonical Structure updateC := leibnizO update.t.

Section heap.
Context `{!heapG Σ}.
Context `{!inG Σ (authR (optionUR (exclR (listO updateC))))}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).
Context `{!forall σ, Timeless (P σ)}.

Definition is_low_state (startpos endpos : u64) (updarray : list update.t) : iProp Σ :=
  ⌜Z.of_nat (length updarray) = LogSz⌝ ∗
  ∃ hdr1 hdr2 hdr2extra,
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    ⌜Block_to_vals hdr1 = b2val <$> encode ([EncUInt64 endpos] ++ (map EncUInt64 (map update.addr updarray)))⌝ ∗
    ⌜Block_to_vals hdr2 = b2val <$> encode [EncUInt64 startpos] ++ hdr2extra⌝ ∗
    2 d↦∗ (update.b <$> updarray).

Definition is_circular_state γ (σ : circΣ.t) : iProp Σ :=
  ∃ (updarray : list update.t),
    own γ (● (Excl' updarray)) ∗
    is_low_state σ.(start) (word.add σ.(start) (length σ.(upds))) updarray ∗
    [∗ list] i ↦ bupd ∈ σ.(upds),
      ⌜updarray !! Z.to_nat ((int.val σ.(start) + i) `mod` LogSz)%Z = Some bupd⌝.

Definition is_circular γ : iProp Σ :=
  inv N (∃ σ, is_circular_state γ σ ∗ P σ).

Definition is_circular_appender γ (circ: loc) : iProp Σ :=
  ∃ s (updarray : list update.t),
    own γ (◯ (Excl' updarray)) ∗
    circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
    is_slice_small s uint64T 1%Qp (u64val <$> (update.addr <$> updarray)).

Opaque encode.

Theorem wp_circular__Advance (Q: iProp Σ) γ d (newStart : u64) :
  {{{ is_circular γ ∗
    (∀ σ, P σ -∗
      ( (∃ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    Advance #d #newStart
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "[#Hcirc Hfupd] HΦ".
  wp_call.
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_apply (wp_Enc__PutInt with "Henc"); [ word | iIntros "Henc" ].
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s) "[Hslice %]".
  wp_apply (wp_Write_fupd _ Q with "[Hslice Hfupd]").
  {
    iDestruct (is_slice_small_sz with "Hslice") as %Hslen.
    rewrite fmap_length in Hslen.

    iSplitL "Hslice".
    { rewrite -list_to_block_to_vals; first iFrame.
      rewrite Hslen. autorewrite with len in H1, Hslen.
      rewrite H0 in H1.
      word.
    }

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray) "(Hγ & Hlow & Hupds)".
    iDestruct "Hlow" as "[% Hlow]".
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra) "(Hd0 & Hd1 & % & % & Hd2)".
    iExists _. iFrame.
    iModIntro.
    iIntros "Hd1".

    iDestruct ("Hfupd" with "HP") as "[Hex Hfupd]".
    iDestruct "Hex" as (eσ' eb) "Hex".
    iDestruct "Hex" as %Hex.

    iSpecialize ("Hfupd" $! eσ' eb).
    simpl in Hex. monad_inv.

    iDestruct ("Hfupd" with "[]") as "Hfupd".
    { iPureIntro. repeat econstructor; lia. }

    iMod "Hfupd" as "[HP HQ]". iFrame.
    iApply "Hclose".

    iNext. iExists _. iFrame.
    iExists _. destruct σ. rewrite /=.
    iSplitL "Hγ"; first iFrame.
    iSplitL "Hd0 Hd1 Hd2".
    { rewrite /is_low_state. iSplitR "Hd0 Hd1 Hd2".
      2: {
        iExists _, _, _. iFrame.
        iPureIntro; destruct_and?; split_and?.
        {
          simpl.
          rewrite H3.
          f_equal. f_equal.
          rewrite skipn_length.
          admit.
        }
        {
          rewrite -list_to_block_to_vals; eauto.
        }
      }
      done.
    }
    admit.
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
Admitted.

Fixpoint apply_updates (updarray : list update.t) (endpos : Z) (newupds : list update.t) : list update.t :=
  match newupds with
  | u :: newupds' =>
    <[ Z.to_nat (endpos `mod` LogSz)%Z := u ]> (apply_updates updarray (endpos+1) newupds')
  | nil => updarray
  end.

Theorem wp_circularAppender__logBlocks γ c d (endpos : u64) (bufs : Slice.t) (updarray : list update.t) diskaddrslice (upds : list update.t) :
  {{{ is_circular γ ∗
      own γ (◯ (Excl' updarray)) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1%Qp (u64val <$> (update.addr <$> updarray)) ∗
      updates_slice bufs upds }}}
    circularAppender__logBlocks #c #d #endpos (slice_val bufs)
  {{{ updarray', RET #();
      own γ (◯ (Excl' updarray')) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1%Qp (u64val <$> (update.addr <$> updarray')) ∗
      updates_slice bufs upds ∗
      ⌜updarray' = apply_updates updarray (int.val endpos) upds⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hcirc & Hγ & Hdiskaddrs & Hslice & Hupdslice) HΦ".
  wp_lam. wp_let. wp_let. wp_let.
  iDestruct "Hupdslice" as (bks) "[Hupdslice Hbks]".

  iDestruct (is_slice_small_sz with "Hupdslice") as %Hslen.
  rewrite fmap_length in Hslen.
  iDestruct (big_sepL2_length with "Hbks") as %Hslen2.

  wp_apply (wp_forSlice (fun i =>
    ∃ updarray',
      own γ (◯ Excl' updarray') ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1%Qp (u64val <$> (update.addr <$> updarray')) ∗
      ( [∗ list] b_upd;upd ∈ bks;upds, let '{| update.addr := a; update.b := b |} := upd in
                                         is_block b_upd.2 b ∗ ⌜b_upd.1 = a⌝) ∗
      ⌜updarray' = apply_updates updarray (int.val endpos) (firstn (int.nat i) upds)⌝)%I
    with "[] [Hγ Hdiskaddrs Hslice Hupdslice Hbks]").

  2: {
    iFrame.
    iExists _. iFrame. 
    rewrite firstn_O /=. done.
  }

  2: {
    iIntros "[Hloop Hupdslice]".
    iDestruct "Hloop" as (updarray') "(Hγ & Hdiskaddrs & Hslice & Hbks & ->)".
    iApply "HΦ".
    iFrame.
    iSplitL "Hbks Hupdslice".
    { iExists _. iFrame. }
    rewrite <- Hslen.
    rewrite Hslen2.
    rewrite firstn_all. done.
  }

  iIntros (i x Φloop) "!> (Hloop & % & %) HΦloop".
  iDestruct "Hloop" as (updarray') "(Hγ & Hdiskaddrs & Hslice & Hbks & ->)".

  wp_pures.

  destruct (list_lookup_lt _ upds (int.nat i)).
  { word. }
  destruct (list_lookup_lt _ bks (int.nat i)).
  { word. }
  rewrite list_lookup_fmap in H1.
  rewrite H3 in H1. simpl in H1. inversion H1; clear H1; subst.
  destruct x1. destruct x0.

  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hi Hbks]"; eauto.
  rewrite /=.
  iDestruct "Hi" as "[Hi ->]".

  rewrite /update_val /=.
Admitted.

Theorem wp_circular__Append (Q: iProp Σ) γ d (endpos : u64) (bufs : Slice.t) (upds : list update.t) c (circAppenderList : list u64) :
  {{{ is_circular γ ∗
      updates_slice bufs upds ∗
      is_circular_appender γ c ∗
      (∀ σ, P σ -∗
        ( (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
          (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    circularAppender__Append #c #d #endpos (slice_val bufs)
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "(#Hcirc & Hslice & Hca & Hfupd) HΦ".
  wp_call.

  iDestruct "Hca" as (addrslice updarray) "(Hγ & Haddrslice & Hs)".
  wp_apply (wp_circularAppender__logBlocks with "[$Hcirc $Hslice $Hγ $Haddrslice $Hs]").

  iIntros (updarray') "(Hγ & Haddrslice & Hs & Hupdslice & ->)".
  wp_apply wp_slice_len.
  wp_pures.
  wp_call.

  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_apply (wp_Enc__PutInt with "Henc"); [ word | iIntros "Henc" ].
  wp_loadField.
  wp_apply (wp_Enc__PutInts with "[$Henc $Hs]").
  {
    admit. (* need more information about number of updates *)
  }
  iIntros "[Henc Hs]".

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s) "[Hslice %]".

  wp_apply (wp_Write_fupd _ Q with "[Hslice Hγ Hfupd]").
  {
    iDestruct (is_slice_small_sz with "Hslice") as %Hslen.
    rewrite fmap_length in Hslen.

    iSplitL "Hslice".
    { rewrite -list_to_block_to_vals; first iFrame.
      rewrite Hslen. admit. (* TODO: avoid reasoning about size of slices, use
      length of list if possible *)
    }

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray0) "(Hγauth & Hlow & Hupds)".
    iDestruct "Hlow" as "[% Hlow]".
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra) "(Hd0 & Hd1 & % & % & Hd2)".
    iExists _. iFrame.
    iModIntro.
    iIntros "Hd0".

    iDestruct (ghost_var_agree with "Hγauth Hγ") as %->.

    iDestruct ("Hfupd" with "HP") as "[Hex Hfupd]".
    iDestruct "Hex" as (eσ' eb) "Hex".
    iDestruct "Hex" as %Hex.

    iSpecialize ("Hfupd" $! eσ' eb).
    simpl in Hex. monad_inv.

    iDestruct ("Hfupd" with "[]") as "Hfupd".
    { iPureIntro. repeat econstructor; lia. }

    iMod "Hfupd" as "[HP HQ]". iFrame.
    iApply "Hclose".

    iNext. iExists _. iFrame.
    iExists _. destruct σ. rewrite /=.
    iSplitL "Hγauth"; first iFrame.
    iSplitL "Hd0 Hd1 Hd2".
    { rewrite /is_low_state. iSplitR "Hd0 Hd1 Hd2".
      2: {
        iExists _, _, _. iFrame.
        iPureIntro; intuition idtac; simpl in *.
        {
          admit.
        }
        {
          eauto.
        }
      }
      done.
    }
    iFrame.
    admit.
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
Admitted.

End heap.
