From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof util_proof.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import GenHeap.

From Perennial.Helpers Require Import Transitions.
Existing Instance r_mbind.

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
  suchThat (gen:=fun _ _ => None) (fun σ _ => P σ).

Definition circ_advance (newStart : u64) : transition circΣ.t unit :=
  assert (fun σ => int.val σ.(start) <= int.val newStart <= int.val σ.(start) + length σ.(upds));;
  modify (fun σ => set upds (drop (Z.to_nat (int.val newStart - int.val σ.(start))%Z)) σ);;
  modify (set start (fun _ => newStart)).

Definition circ_append (l : list update.t) (endpos : u64) : transition circΣ.t unit :=
  assert (fun σ => circΣ.diskEnd σ = int.val endpos);;
  assert (fun σ => circΣ.diskEnd σ + length l < 2^64);;
  modify (set circΣ.upds (fun u => u ++ l));;
  assert (fun σ => length σ.(upds) <= LogSz).

Canonical Structure updateO := leibnizO update.t.


Section heap.
Context `{!heapG Σ}.
Context `{!inG Σ (authR (optionUR (exclR (listO updateO))))}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).
Context {Ptimeless: forall σ, Timeless (P σ)}.

Definition is_low_state (startpos endpos : u64) (updarray : list update.t) : iProp Σ :=
  ⌜Z.of_nat (length updarray) = LogSz⌝ ∗
  ∃ hdr1 hdr2 hdr2extra,
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    ⌜Block_to_vals hdr1 = b2val <$> encode ([EncUInt64 endpos] ++ (map EncUInt64 (update.addr <$> updarray)))⌝ ∗
    ⌜Block_to_vals hdr2 = b2val <$> encode [EncUInt64 startpos] ++ hdr2extra⌝ ∗
    2 d↦∗ (update.b <$> updarray).

Definition has_circ_updates (start: Z) (upds: list update.t) (updarray: list update.t) :=
  forall i bupd, upds !! i = Some bupd ->
            updarray !! (Z.to_nat $ (start + Z.of_nat i) `mod` LogSz) = Some bupd.

Definition is_circular_state γ (σ : circΣ.t) : iProp Σ :=
  ∃ (updarray : list update.t),
    own γ (● (Excl' updarray)) ∗
    is_low_state σ.(start) (word.add σ.(start) (length σ.(upds))) updarray ∗
    ⌜int.val σ.(start) + length σ.(upds) < 2^64⌝ ∗
    ⌜has_circ_updates (int.val σ.(start)) σ.(upds) updarray⌝.

Definition is_circular γ : iProp Σ :=
  inv N (∃ σ, is_circular_state γ σ ∗ P σ).

Definition is_circular_appender γ (circ: loc) : iProp Σ :=
  ∃ s (updarray : list update.t),
    own γ (◯ (Excl' updarray)) ∗
    circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
    is_slice_small s uint64T 1 (u64val <$> (update.addr <$> updarray)).

Lemma is_low_state_array_len startpos endpos updarray :
  is_low_state startpos endpos updarray -∗ ⌜Z.of_nat (length updarray) = LogSz⌝.
Proof.
  iIntros "[% _]".
  done.
Qed.

Theorem updarray_len γ updarray :
  is_circular γ -∗ own γ (◯ (Excl' updarray)) ={⊤}=∗ ⌜Z.of_nat (length updarray) = LogSz⌝ ∗ own γ (◯ (Excl' updarray)).
Proof using Ptimeless.
  iIntros "#Hcirc Hown".
  iInv "Hcirc" as ">Hcircular".
  iDestruct "Hcircular" as (σ) "[Hcs HP]".
  iDestruct "Hcs" as (updarray') "(Hγ & Hlow & Hupds)".
  iDestruct (ghost_var_agree with "Hγ Hown") as %->.
  iDestruct (is_low_state_array_len with "Hlow") as %Hlen.
  iModIntro.
  iSplitR "Hown".
  { iNext; iExists σ; iFrame.
    iExists updarray; iFrame. }
  iFrame.
  done.
Qed.

Lemma has_circ_updates_advance:
  ∀ (newStart : u64) (upds : list update.t) (start : u64) (updarray : list update.t),
    has_circ_updates (int.val start) upds updarray
    → int.val start ≤ int.val newStart ∧ int.val newStart ≤ int.val start + strings.length upds
    → has_circ_updates (int.val newStart) (drop (Z.to_nat (int.val newStart - int.val start)) upds)
                       updarray.
Proof.
  rewrite /has_circ_updates; intros.
  rewrite lookup_drop in H1.
  pose proof (lookup_lt_Some _ _ _ H1).
  apply H in H1.
  match goal with
  | [ H: updarray !! ?i = Some _ |- updarray !! ?i' = Some _ ] =>
    replace i' with i; [ exact H | ]
  end.
  f_equal.
  f_equal.
  lia.
Qed.

Opaque encode.

Theorem wp_circular__Advance (Q: iProp Σ) γ d (newStart : u64) :
  {{{ is_circular γ ∗
    (∀ σ, P σ -∗
      ( (∃ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    Advance #d #newStart
  {{{ RET #(); Q }}}.
Proof using Ptimeless.
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
      rewrite Hslen. autorewrite with len in H0, Hslen.
      rewrite H in H0.
      word.
    }

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray) "(Hγ & Hlow & Hupds)".
    iDestruct "Hupds" as %(Hendpos&Hupds).
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

    iMod ("Hfupd" with "[]") as "[HP HQ]".
    { iPureIntro. repeat econstructor; lia. }
    iFrame.
    iApply "Hclose".

    iNext. iExists _. iFrame.
    iExists _.
    iFrame "Hγ". destruct σ. rewrite /=.
    iSplitL "Hd0 Hd1 Hd2".
    { rewrite /is_low_state. iSplitR "Hd0 Hd1 Hd2"; first by done.
      iExists _, _, _. iFrame.
      iPureIntro; destruct_and?; split_and?.
      {
        simpl.
        rewrite H2.
        f_equal. f_equal.
        rewrite drop_length.
        simpl in *; f_equal.
        f_equal.
        word.
      }
      rewrite -list_to_block_to_vals; eauto.
    }
    iPureIntro.
    simpl in *.
    split.
    { len. }
    apply has_circ_updates_advance; auto.
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
  Grab Existential Variables.
  all: auto.
Qed.

Fixpoint apply_updates (updarray : list update.t) (endpos : Z) (newupds : list update.t) : list update.t :=
  match newupds with
  | u :: newupds' =>
    <[ Z.to_nat (endpos `mod` LogSz)%Z := u ]> (apply_updates updarray (endpos+1) newupds')
  | nil => updarray
  end.

Lemma apply_updates_length updarray endpos upds :
  length (apply_updates updarray endpos upds) = length updarray.
Proof.
  revert endpos updarray.
  induction upds; simpl; intros; len.
  rewrite IHupds //.
Qed.

Hint Rewrite apply_updates_length : len.

Ltac invc H := inversion H; subst; clear H.

Opaque struct.get.

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
    with "[] [Hγ Hdiskaddrs Hslice Hupdslice $Hbks]").

  2: {
    iFrame.
    iExists _. iFrame.
    rewrite take_0 //.
  }

  2: {
    iIntros "[Hloop Hupdslice]".
    iDestruct "Hloop" as (updarray') "(Hγ & Hdiskaddrs & Hslice & Hbks & ->)".
    iApply "HΦ".
    iFrame.
    iSplitL "Hbks Hupdslice".
    { iExists _. iFrame. }
    iPureIntro.
    rewrite -> take_ge by lia; auto.
  }

  iIntros (i x Φloop) "!> (Hloop & % & %) HΦloop".
  iDestruct "Hloop" as (updarray') "(Hγ & Hdiskaddrs & Hslice & Hbks & ->)".

  wp_pures.

  destruct (list_lookup_lt _ upds (int.nat i)).
  { word. }
  destruct (list_lookup_lt _ bks (int.nat i)).
  { word. }
  rewrite list_lookup_fmap in H0.
  rewrite H2 /= in H0. inversion H1; clear H1; subst.
  destruct x1. destruct x0.

  iDestruct (big_sepL2_insert_acc with "Hbks") as "[Hi Hbks]"; eauto.
  rewrite /=.
  iDestruct "Hi" as "[Hi ->]".
  invc H0.
  wp_apply wp_getField; auto.
  wp_apply wp_getField; auto.
  wp_pures.
  wp_apply wp_DPrintf.
  wp_pures.
  change (word.divu (word.sub 4096 8) 8) with (U64 511).
  (* TODO: need to use a HOCAP Write spec since the disk points-to is in an invariant *)
  wp_apply wp_Write_fupd.
Admitted.

Theorem apply_updates_lookup_new updarray endpos newupds (i: nat) u :
  forall (Hendpos_ge: 0 <= endpos)
    (Hlen: length updarray = Z.to_nat LogSz)
    (Hnewlen: length newupds <= LogSz)
    (Hlookup: newupds !! i = Some u),
    apply_updates updarray endpos newupds
                  !! Z.to_nat ((endpos + Z.of_nat i) `mod` LogSz)
    = Some u.
Proof.
  revert endpos i.
  induction newupds; simpl; intros.
  - rewrite lookup_nil in Hlookup; congruence.
  - destruct (decide (i = O)); subst.
    + inversion Hlookup; subst; clear Hlookup.
      rewrite Z.add_0_r.
      rewrite list_lookup_insert; auto.
      rewrite /LogSz in Hlen |- *.
      len.
      pose proof (Z.mod_bound_pos endpos 511).
      lia.
    + rewrite list_lookup_insert_ne; auto.
      { replace (endpos + i) with (endpos + 1 + Z.of_nat (i - 1)) by lia.
        eapply IHnewupds; eauto; try lia.
        replace i with (S (i - 1)%nat) in Hlookup by lia.
        simpl in Hlookup; auto. }
      apply lookup_lt_Some in Hlookup.
      simpl in Hlookup.
      assert (i < Z.to_nat LogSz)%nat.
      { lia. }
      intro.
      pose proof (Z.mod_bound_pos endpos LogSz ltac:(lia) ltac:(lia)).
      pose proof (Z.mod_bound_pos (endpos + i) LogSz ltac:(lia) ltac:(lia)).
      apply Z2Nat.inj in H0; try lia.
      assert (Z.of_nat i < LogSz) by lia.
      (* endpos%511 = (endpos+i)%511 but i<511, contradiction *)
Admitted.

Lemma has_circ_updates_append:
  ∀ (endpos : u64) (upds updarray upds0 : list update.t) (start : u64),
    strings.length (upds0 ++ upds) ≤ LogSz
    -> length updarray = Z.to_nat LogSz
    -> int.val start + length upds0 = int.val endpos
    → has_circ_updates (int.val start) upds0 (apply_updates updarray (int.val endpos) upds)
    → has_circ_updates (int.val start) (upds0 ++ upds)
                       (apply_updates updarray (int.val endpos) upds).
Proof.
  unfold has_circ_updates.
  intros.
  destruct (decide (i < length upds0)).
  { apply H2.
    rewrite -> lookup_app_l in H3 by lia.
    auto.
  }
  rewrite -> lookup_app_r in H3 by lia.
  replace (int.val endpos).
  replace (int.val start + i) with
      (int.val start + length upds0 + (Z.of_nat $ (i - length upds0)%nat)) by lia.
  autorewrite with len in H.
  eapply apply_updates_lookup_new; eauto; len.
Qed.

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
Proof using Ptimeless.
  iIntros (Φ) "(#Hcirc & Hslice & Hca & Hfupd) HΦ".
  wp_call.

  iDestruct "Hca" as (addrslice updarray) "(Hγ & Haddrslice & Hs)".
  iMod (updarray_len with "Hcirc Hγ") as (Hupdarray_len) "Hγ".
  wp_apply (wp_circularAppender__logBlocks with "[$Hcirc $Hslice $Hγ $Haddrslice $Hs]").

  iIntros (updarray') "(Hγ & Haddrslice & Hs & Hupdslice & ->)".
  wp_apply wp_slice_len.
  wp_pures.
  wp_call.
  iDestruct (updates_slice_len with "Hupdslice") as %Hbufslen.

  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_apply (wp_Enc__PutInt with "Henc"); [ word | iIntros "Henc" ].
  wp_loadField.
  wp_apply (wp_Enc__PutInts with "[$Henc $Hs]").
  {
    len.
    rewrite Hupdarray_len.
    rewrite /LogSz.
    word.
  }
  iIntros "[Henc Hs]".

  wp_apply (wp_Enc__Finish_complete with "Henc").
  { len.
    rewrite Hupdarray_len.
    rewrite /LogSz.
    word. }
  iIntros (s) "[Hslice %]".

  wp_apply (wp_Write_fupd _ Q with "[Hslice Hγ Hfupd]").
  {
    iDestruct (is_slice_small_sz with "Hslice") as %Hslen.
    rewrite fmap_length in H0.

    iSplitL "Hslice".
    { rewrite -list_to_block_to_vals; first iFrame.
      rewrite H0 H //. }

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray0) "(Hγauth & Hlow & Hupds)".
    iDestruct "Hupds" as %Hupds.
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
        len.
        iPureIntro; (intuition idtac); simpl in *.
        {
          rewrite list_to_block_to_vals.
          { f_equal. f_equal. f_equal. f_equal.
            rewrite /circΣ.diskEnd /= in H4, H5.
            autorewrite with len in *.
            word.
          }
          autorewrite with len in H0, Hslen.
          rewrite H in H0.
          word.
        }
        rewrite H3; eauto.
      }
      simpl in *.
      autorewrite with len in *.
      done.
    }
    iPureIntro.
    (intuition idtac); len.
    { simpl in *.
      rewrite /circΣ.diskEnd /= in H4, H5.
      lia. }
    { simpl in *.
      rewrite /circΣ.diskEnd /= in H4.
      apply has_circ_updates_append; eauto.
      autorewrite with len in *; len. }
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
  Grab Existential Variables.
  all: auto.
Qed.

End heap.
