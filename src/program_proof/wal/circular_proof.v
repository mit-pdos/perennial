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

Fixpoint apply_update_blocks (updarray : list update.t) (endpos : Z) (newupds : list update.t) : list update.t :=
  match newupds with
  | u :: newupds' =>
    alter (fun '(update.mk addr b) => update.mk addr u.(update.b)) (Z.to_nat (endpos `mod` LogSz)) (apply_update_blocks updarray (endpos+1) newupds')
  | nil => updarray
  end.

Hint Rewrite @alter_length : len.

Lemma apply_update_blocks_length updarray endpos upds :
  length (apply_update_blocks updarray endpos upds) = length updarray.
Proof.
  revert endpos updarray.
  induction upds; simpl; intros; len.
  rewrite IHupds //.
Qed.

Hint Rewrite apply_update_blocks_length : len.

Theorem update_blocks_addrs updarray endpos newupds :
  update.addr <$> apply_update_blocks updarray endpos newupds = update.addr <$> updarray.
Proof.
  revert endpos.
  induction newupds; simpl; intros; auto.
  - erewrite (list_alter_fmap _ _ id); eauto.
    { rewrite IHnewupds.
      rewrite list_alter_id; auto. }
    apply Forall_forall; intros.
    destruct x; simpl; auto.
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

Lemma mod_add_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a + k) `mod` k.
Proof.
  intros.
  rewrite -> Z.add_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.add_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
Qed.

Lemma mod_sub_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a - k) `mod` k.
Proof.
  intros.
  rewrite -> Zminus_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.sub_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
Qed.

Theorem mod_neq_lt a b k :
  0 < k ->
  0 <= a < b ->
  b - a < k ->
  a `mod` k ≠ b `mod` k.
Proof.
  intros.
  assert (k ≠ 0) by lia.
  replace b with (a + (b - a)) by lia.
  assert (0 < b - a) by lia.
  generalize dependent (b - a); intros d **.
  intros ?.
  assert ((a + d) `mod` k - a `mod` k = 0) by lia.
  assert (((a + d) `mod` k - a `mod` k) `mod` k = 0).
  { rewrite H5.
    rewrite Z.mod_0_l; lia. }
  rewrite -Zminus_mod in H6.
  replace (a + d - a) with d in H6 by lia.
  rewrite -> Z.mod_small in H6 by lia.
  lia.
Qed.

Theorem mod_neq_gt a b k :
  0 < k ->
  0 <= a < b ->
  b - a < k ->
  b `mod` k ≠ a `mod` k.
Proof.
  intros ** Heq%eq_sym%mod_neq_lt; lia.
Qed.

Theorem Zto_nat_neq_inj z1 z2 :
  0 <= z1 ->
  0 <= z2 ->
  z1 ≠ z2 ->
  Z.to_nat z1 ≠ Z.to_nat z2.
Proof.
  lia.
Qed.

Theorem LogSz_gt_0 : 0 < LogSz.
Proof. reflexivity. Qed.
Hint Resolve LogSz_gt_0 : core.

Theorem mod_LogSz_pos z : 0 <= z `mod` LogSz.
Proof. apply Z_mod_pos, LogSz_gt_0. Qed.

Hint Resolve mod_LogSz_pos : core.

Theorem apply_updates_lookup_old (start: Z) updarray endpos newupds (i: Z) :
  0 <= i ->
  0 <= start + i < endpos ->
  endpos + length newupds - start <= LogSz ->
  apply_updates updarray endpos newupds !! Z.to_nat ((start + i) `mod` LogSz) =
  updarray !! Z.to_nat ((start + i) `mod` LogSz).
Proof.
  revert endpos start i.
  induction newupds; simpl; intros; auto.
  rewrite list_lookup_insert_ne.
  { erewrite IHnewupds; eauto; try lia. }
  apply Zto_nat_neq_inj; eauto.
  apply mod_neq_gt; eauto; try lia.
Qed.

Theorem apply_update_blocks_lookup_old (start: Z) updarray endpos newupds (i: Z) :
  0 <= i ->
  0 <= start + i < endpos ->
  endpos + length newupds - start <= LogSz ->
  apply_update_blocks updarray endpos newupds !! Z.to_nat ((start + i) `mod` LogSz) =
  updarray !! Z.to_nat ((start + i) `mod` LogSz).
Proof.
  revert endpos start i.
  induction newupds; simpl; intros; auto.
  rewrite list_lookup_alter_ne.
  { erewrite IHnewupds; eauto; try lia. }
  apply Zto_nat_neq_inj; eauto.
  apply mod_neq_gt; eauto; try lia.
Qed.

Theorem apply_update_blocks_lookup_new updarray endpos newupds (i: Z) :
  0 <= endpos ->
  0 <= i < length newupds ->
  length newupds <= length updarray ->
  Z.of_nat (length updarray) = LogSz ->
  update.b <$> apply_update_blocks updarray endpos newupds !! Z.to_nat ((endpos + i) `mod` LogSz) =
  update.b <$> newupds !! Z.to_nat i.
Proof.
  revert endpos i.
  induction newupds; simpl; intros; auto.
  { lia. }
  destruct (decide (i = 0)); subst.
  - rewrite Z.add_0_r.
    rewrite list_lookup_alter.
    simpl.
    destruct (list_lookup_lt _ (apply_update_blocks updarray (endpos + 1) newupds) (Z.to_nat (endpos `mod` LogSz))) as [[a0 b0] Hu].
    { len.
      pose proof (Z.mod_bound_pos endpos LogSz).
      word. }
    rewrite Hu //=.
  - replace (endpos + i) with (endpos + 1 + (i-1)) by lia.
    rewrite list_lookup_alter_ne.
    { rewrite IHnewupds; try lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
      rewrite -?list_lookup_fmap //. }
    apply Zto_nat_neq_inj; auto; try lia.
    apply mod_neq_lt; lia.
Qed.

Theorem apply_update_blocks_lookup_past_end updarray endpos newupds (i: Z) :
  0 <= endpos ->
  length newupds <= i < LogSz ->
  apply_update_blocks updarray endpos newupds !! Z.to_nat ((endpos + i) `mod` LogSz) =
  updarray !! Z.to_nat ((endpos + i) `mod` LogSz).
Proof.
  revert endpos i.
  induction newupds; simpl; intros; auto.
  replace (endpos + i) with (endpos + 1 + (i-1)) by lia.
  rewrite list_lookup_alter_ne.
  { rewrite IHnewupds; auto; lia. }
  apply Zto_nat_neq_inj; auto; try lia.
  apply mod_neq_lt; auto; lia.
Qed.

Lemma apply_update_blocks_app1 updarray endpos newupds u:
  apply_update_blocks updarray endpos (newupds ++ [u]) =
  apply_update_blocks (alter (fun '(update.mk addr b) => update.mk addr u.(update.b)) (Z.to_nat ((endpos + length newupds) `mod` LogSz)) updarray) endpos newupds.
Proof.
  revert updarray endpos.
  induction newupds; simpl; intros.
  { rewrite Z.add_0_r //. }
  rewrite IHnewupds.
  repeat (f_equal; try lia).
Qed.

Lemma has_circ_updates_log_one:
  ∀ (endpos : u64) (updarray newupds : list update.t) (i: u64) upd,
    newupds !! int.nat i = Some upd ->
    ∀ σ : circΣ.t,
      int.val (start σ) <= int.val endpos ->
      int.val endpos = int.val (start σ) + length (circΣ.upds σ) ->
      (* why is this < and not ≤? *)
      int.val endpos + Z.of_nat (length newupds) - int.val (start σ) < LogSz ->
      has_circ_updates (int.val (start σ)) (circΣ.upds σ)
                       (apply_update_blocks updarray (int.val endpos) (take (int.nat i) newupds)) ->
      has_circ_updates (int.val (start σ)) (circΣ.upds σ)
                       (apply_update_blocks updarray (int.val endpos) (take (S (int.nat i)) newupds)).
Proof.
  intros.
  assert (0 <= int.val (start σ)) by word.
  generalize dependent (int.val (start σ)); intros start.
  generalize dependent (circΣ.upds σ); intros upds.
  assert (0 <= int.val endpos) by word.
  generalize dependent (int.val endpos); clear endpos; intros endpos.
  intros **.
  clear σ.
  erewrite take_S_r; eauto.
  rewrite apply_update_blocks_app1.
  unfold has_circ_updates; intros.
  pose proof (lookup_lt_Some _ _ _ H6).
  apply H4 in H6.
  rewrite apply_update_blocks_lookup_old; len; try lia.
  rewrite apply_update_blocks_lookup_old in H6; len; try lia.
  rewrite list_lookup_alter_ne; auto.
  apply Zto_nat_neq_inj; eauto.
  apply mod_neq_gt; eauto; try lia.
Qed.

Lemma apply_update_blocks_insert:
  ∀ (endpos : Z) (updarray upds : list update.t) (i : Z) (b : Block),
    0 <= endpos ->
    0 <= i <= length upds ->
    i < LogSz ->
    update.b <$>
             apply_update_blocks
             (alter (λ '{| update.addr := addr |}, {| update.addr := addr; update.b := b |})
                    (Z.to_nat ((endpos + length (take (Z.to_nat i) upds)) `mod` LogSz)) updarray)
             (endpos) (take (Z.to_nat i) upds) =
    <[Z.to_nat ((endpos + i) `mod` LogSz):=b]>
    (update.b <$> apply_update_blocks updarray endpos (take (Z.to_nat i) upds)).
Proof.
  intros.
  remember (take (Z.to_nat i) upds) as newupds.
  assert (Z.of_nat (length newupds) = i) by (subst; len).
  destruct H0 as [H0 _].
  clear Heqnewupds.
  clear upds.

  generalize dependent i.
  generalize dependent endpos.
  induction newupds as [|u newupds]; simpl; intros.
  - assert (i = 0) by word; subst.
    rewrite Z.add_0_r.
    rewrite (list_alter_fmap _ _ (λ _, b)); eauto.
    { rewrite list_insert_alter //. }
    apply Forall_forall; intros.
    destruct x; auto.
  - rewrite (list_alter_fmap _ _ (λ _, u.(update.b))); eauto.
    2: {
      apply Forall_forall; intros.
      destruct x; auto.
    }
    replace (endpos + S (length newupds)) with
        (endpos + 1 + length newupds) by lia.
    replace (endpos + i) with (endpos + 1 + (length newupds)) by lia.
    rewrite (IHnewupds (endpos + 1) _ (i - 1)); try lia.
    replace (endpos + 1 + (i - 1)) with (endpos + i) by lia.
    replace (endpos + 1 + length newupds) with (endpos + i) by lia.
    rewrite (list_alter_fmap _ _ (λ _, u.(update.b))); eauto.
    2: {
      apply Forall_forall; intros.
      destruct x; auto.
    }
    rewrite -?list_insert_alter.
    rewrite list_insert_commute; eauto.
    apply Zto_nat_neq_inj; auto.
    apply mod_neq_lt; eauto; try lia.
Qed.

Ltac invc H := inversion H; subst; clear H.
Opaque struct.get.

Theorem wp_circularAppender__logBlocks γ c d (endpos : u64) (bufs : Slice.t) (updarray : list update.t) diskaddrslice (upds : list update.t) :
  {{{ is_circular γ ∗
      own γ (◯ (Excl' updarray)) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> (update.addr <$> updarray)) ∗
      updates_slice bufs upds }}}
    circularAppender__logBlocks #c #d #endpos (slice_val bufs)
  {{{ updarray', RET #();
      own γ (◯ (Excl' updarray')) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> (update.addr <$> updarray')) ∗
      updates_slice bufs upds ∗
      ⌜updarray' = apply_update_blocks updarray (int.val endpos) upds⌝
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
      is_slice_small diskaddrslice uint64T 1 (u64val <$> (update.addr <$> updarray')) ∗
      ( [∗ list] b_upd;upd ∈ bks;upds, let '{| update.addr := a; update.b := b |} := upd in
                                         is_block b_upd.2 b ∗ ⌜b_upd.1 = a⌝) ∗
      ⌜updarray' = apply_update_blocks updarray (int.val endpos) (take (int.nat i) upds)⌝)%I
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
  change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
  let updarray' := constr:(apply_update_blocks updarray (int.val endpos) (take (S (int.nat i)) upds)) in
  wp_apply (wp_Write_fupd (⊤ ∖ ↑N) (own γ (◯ Excl' updarray')) with "[$Hi Hγ]").
  {
    iInv "Hcirc" as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[Hcs HP]".
    iDestruct "Hcs" as (updarray0) "(Hγauth & Hlow & Hupds)".
    iDestruct "Hupds" as %Hupds.
    iDestruct "Hlow" as "[% Hlow]".
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra) "(Hd0 & Hd1 & % & % & Hd2)".
    iDestruct (ghost_var_agree with "Hγauth Hγ") as %->.
    autorewrite with len in *.
    (* TODO: need a precondition constraining length upds *)
    assert (int.val i < LogSz) by admit.
    pose proof (lookup_lt_Some _ _ _ H4).
    destruct (list_lookup_lt _ updarray (Z.to_nat ((int.val endpos + int.val i) `mod` LogSz))) as [u Hupdarray_i].
    { pose proof (Z.mod_bound_pos (int.val endpos + int.val i) LogSz); word. }
    iDestruct (update_disk_array _ _ ((int.val endpos + int.val i) `mod` LogSz) with "[$Hd2]") as "[Hdi Hd2]".
    { auto. }

    { rewrite list_lookup_fmap.
      rewrite -> apply_update_blocks_lookup_past_end; try len.
      eapply fmap_Some_2; eauto. }

    word_cleanup; try (unfold LogSz; word).
    assert (2 + (int.val endpos + int.val i) `mod` LogSz =
            word.wrap (word:=u64_instance.u64) (2 + int.val (word.add endpos i) `mod` LogSz)) as Hiaddr by admit.
    rewrite -Hiaddr.
    iModIntro.
    iExists u.(update.b).
    iFrame "Hdi".
    iIntros "Hdi".
    iSpecialize ("Hd2" with "Hdi").
    iMod (ghost_var_update γ (apply_update_blocks updarray (int.val endpos)
                           (take (S (int.nat i)) upds)) with "Hγauth Hγ") as "[Hγauth Hγ]".
    iFrame.
    iApply "Hclose".
    iNext.
    iExists _; iFrame.
    iExists _; iFrame.
    iSplitL; auto.
    { iSplitR; first by len.
      iExists _, _, _; iFrame.
      iSplitR; [ | iSplitR ].
      - rewrite ?update_blocks_addrs in H1 |- *.
        auto.
      - iPureIntro.
        eauto.
      - iExactEq "Hd2".
        f_equal.
        erewrite take_S_r; eauto.
        rewrite apply_update_blocks_app1.
        simpl.
        rewrite apply_update_blocks_insert; try word.
        auto.
    }
    iPureIntro.
    split; try word.
    destruct Hupds.
    (* TODO: oops, this works poorly (none of these bounds are in the
    invariant) *)
    (* eapply has_circ_updates_log_one; eauto; try word. *)
    admit.
  }
  iIntros "[Hs Hγ]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hslice]").
  { iPureIntro.
    split; [ | val_ty ].
    change (word.divu (word.sub 4096 8) 8) with (U64 511).
    word_cleanup.
    apply lookup_lt_is_Some_2; len.
    pose proof (Z.mod_bound_pos (int.val (word.add endpos i)) 511).
    replace (length updarray) with 511%nat by admit.
    lia.
  }
  iIntros "Hslice".
  iApply "HΦloop".
  iExists _; iFrame.
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
    (* TODO: make this work *)
    (* iMod (ghost_var_update γ (apply_updates updarray (int.val endpos) upds)
            with "Hγauth Hγ") as "[Hγauth Hγ]". *)

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
      (* TODO: this will only work after the above ghost_var_update *)
      (* apply has_circ_updates_append; eauto.
      autorewrite with len in *; len. *)
      admit. }
  }

  iIntros "[Hslice HQ]".
  wp_pures.
  wp_call.
  iApply "HΦ".
  iFrame.
  Grab Existential Variables.
  all: auto.
Admitted.

End heap.
