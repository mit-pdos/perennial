From Perennial.base_logic.lib Require Import mono_nat.
From Perennial.Helpers Require Import Transitions NamedProps Map gset range_set.
From Perennial.algebra Require Import auth_map log_heap.
From Perennial.base_logic Require Import lib.ghost_map.

From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.go_journal Require Import obj.
From Goose.github_com.mit_pdos.go_journal Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Import obj.invariant.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang Require Import crash_modality.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Section goose_lang.
Context `{!txnG Σ}.
Context `{!heapGS Σ}.

Implicit Types (γ: txn_names).

Definition txn_init_ghost_state γ : iProp Σ :=
  let logm0 := Build_async (∅: gmap addr object) [] in
  "logheap" ∷ ghost_map_auth γ.(txn_logheap) 1 (latest logm0) ∗
  "crashstates" ∷ ghost_var γ.(txn_crashstates) 1 logm0 ∗
  "metaheap" ∷ map_ctx γ.(txn_metaheap) 1 (∅ : gmap addr gname).

Lemma alloc_txn_init_ghost_state (γtxn_walnames: wal_heap_gnames) kinds :
  ⊢ |==> ∃ γ, ⌜γ.(txn_walnames) = γtxn_walnames⌝ ∗
              ⌜γ.(txn_kinds) = kinds⌝ ∗
              txn_init_ghost_state γ.
Proof.
  set (logm:=Build_async (∅: gmap addr object) []).
  iMod (ghost_map_alloc (latest logm)) as (txn_logheap) "[? _]".
  iMod (ghost_var_alloc logm) as (txn_crashstates) "?".
  iMod (map_init (∅ : gmap addr gname)) as (txn_metaheap) "?".
  iModIntro.
  iExists (Build_txn_names _ _ _ _ _).
  rewrite /txn_init_ghost_state /=.
  by iFrame.
Qed.

Definition is_txn_durable γ dinit : iProp Σ :=
  ∃ ls' logm crash_heaps,
  "%Hpostcrash" ∷ ⌜ wal_post_crash ls' ⌝ ∗
  "His_wal_inner_durable" ∷ is_wal_inner_durable γ.(txn_walnames).(wal_heap_walnames) ls' dinit ∗
  "Hwal_res" ∷ wal_resources γ.(txn_walnames).(wal_heap_walnames) ∗
  "Hwal_heap_inv" ∷ wal_heap_inv γ.(txn_walnames) ls' ∗
  "Hlocked_walheap" ∷ is_locked_walheap γ.(txn_walnames) {| locked_wh_σd := ls'.(log_state.d);
                        locked_wh_σtxns := ls'.(log_state.txns);
                    |} ∗
  "His_txn_always" ∷ is_txn_state γ logm crash_heaps.


Definition inode0_map : gmap u64 object :=
  gset_to_gmap (existT _ (bufInode inode_buf0))
               (list_to_set $ (λ i, U64 (i*8*128)%Z) <$> (seqZ 0 32)).

Definition bit0_map : gmap u64 object :=
  gset_to_gmap (existT _ (bufBit false))
               (list_to_set $ U64 <$> seqZ 0 (8*block_bytes)).

Definition block0_map : gmap u64 object :=
  {[U64 0 := existT _ (bufBlock block0)]}.

Definition kind_heap0 (kinds: gmap u64 bufDataKind) : gmap addr object :=
  gmap_curry ((λ K, match K with
                   | KindBit => bit0_map
                   | KindInode => inode0_map
                   | KindBlock => block0_map
                   end) <$> kinds).

Lemma repeat_to_replicate {A} (x:A) n :
  repeat x n = replicate n x.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma crash_heap0_repeat_block0 (sz: nat) :
  513 + sz < 2^64 →
  crash_heap0 (repeat block0 sz) = gset_to_gmap block0 (rangeSet 513 (Z.of_nat sz)).
Proof.
  rewrite repeat_to_replicate.
  intros Hbound.
  rewrite /crash_heap0.
  apply map_eq; intros i.
  apply option_eq; intros b.
  rewrite lookup_gset_to_gmap.
  rewrite lookup_list_to_map.
  - rewrite elem_of_lookup_imap.
    setoid_rewrite lookup_replicate.
    destruct (decide (i ∈ rangeSet 513 sz));
    try (rewrite -> option_guard_True by done);
    try (rewrite -> option_guard_False by done).
    + apply rangeSet_lookup in e; [ | word .. ].
      split; [ naive_solver | ].
      inversion 1; subst.
      eexists (Z.to_nat (int.Z i - 513)), _.
      split_and!; eauto; try lia.
      f_equal; word.
    + rewrite -> rangeSet_lookup in n by word.
      split; [ | inversion 1 ]; intros.
      destruct H as (i' & b' & [=] & ? & ?); subst.
      move: n; word.
  - rewrite fst_imap.
    rewrite replicate_length.
    eapply NoDup_fmap_2_strong; last by eapply NoDup_seq.
    intros x y Hx Hy Heq.
    eapply elem_of_seq in Hx.
    eapply elem_of_seq in Hy.
    assert (int.Z (U64 (513 + Z.of_nat x)) = int.Z (U64 (513 + Z.of_nat y))).
    { rewrite Heq. eauto. }
    revert H. word.
Qed.

Lemma alloc_metamap names (m: gmap addr object):
  map_ctx names 1 ∅ ==∗
  ∃ metam,
  map_ctx names 1 metam ∗
  ([∗ map] addr↦bufData;γm ∈ m;metam, ghost_var γm (1/2) true) ∗
  ([∗ map] addr↦bufData;γm ∈ m;metam, ptsto_mut names addr 1 γm ∗ ghost_var γm (1/2) true).
Proof.
  iIntros "Hctx".
  iInduction m as [|i x m] "IH" using map_ind.
  - iExists ∅. rewrite ?big_sepM2_empty //. by iFrame.
  - iMod ("IH" with "Hctx") as (metam) "(H1&H2&H3)".
    iDestruct (big_sepM2_dom with "H2") as %Hdom.
    iMod (ghost_var_alloc true) as (γm) "[Hm1 Hm2]".
    assert (metam !! i = None).
    { apply not_elem_of_dom. rewrite -Hdom.
      apply not_elem_of_dom. eauto. }
    iMod (map_alloc i γm with "[$]") as "(Hctx&Hpts)"; auto.
    iExists (<[i := γm]>metam).
    iFrame. iSplitL "H2 Hm1".
    { rewrite big_sepM2_insert //. by iFrame. }
    { rewrite big_sepM2_insert //. by iFrame. }
Qed.

Theorem mapsto_txn_alloc {T} (γ : gname) (logm : gmap addr T) :
  map_ctx γ 1 ∅
  ==∗
  ∃ m,
    ⌜dom (gset addr) m = dom (gset addr) logm⌝ ∗
    map_ctx γ 1 m ∗
    ([∗ map] a↦_ ∈ logm, ∃ (γm : gname), a [[γ]]↦ γm ∗ ghost_var γm (1/2) true) ∗
    ([∗ map] _↦γm ∈ m, ghost_var γm (1/2) true).
Proof.
  iIntros "H".
  iInduction logm as [|a v m] "IH" using map_ind.
  { iModIntro. iExists _. iFrame. rewrite !big_sepM_empty. rewrite !dom_empty_L. done. }
  iMod ("IH" with "H") as (m0) "(%Hdom & H & H0 & H1)".
  assert (m0 !! a = None).
  { apply not_elem_of_dom in H. apply not_elem_of_dom. rewrite Hdom. eauto. }
  iMod (ghost_var_alloc true) as (γm) "[Hγ0 Hγ1]".
  iMod (map_alloc a γm with "H") as "[H Ha]"; eauto.
  iModIntro. iExists _. iFrame "H". iSplit.
  { iPureIntro. rewrite !dom_insert_L Hdom. done. }
  iSplitL "H0 Hγ0 Ha".
  { iApply big_sepM_insert; eauto. iFrame. iExists _. iFrame. }
  iApply big_sepM_insert; eauto. iFrame.
Qed.

Hint Rewrite repeat_length : len.

Lemma block_bytes_pos : 0 < Z.of_nat block_bytes.
Proof. rewrite /block_bytes. lia. Qed.

Lemma lookup_bit0_map (off: u64) o :
  bit0_map !! off = Some o ↔
  int.Z off < block_bytes * 8 ∧
  o = existT KindBit (bufBit false).
Proof.
  rewrite /bit0_map.
  rewrite lookup_gset_to_gmap_Some.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seqZ.
  change block_bytes with (Z.to_nat 4096).
  split; intros.
  - intuition (subst; auto).
    destruct H0 as [off' [? ?]]; subst.
    word.
  - intuition (subst; auto).
    exists (int.Z off); split; word.
Qed.

Lemma lookup_inode0_map (off: u64) o :
  inode0_map !! off = Some o ↔
  ∃ (i:Z), i < 32 ∧
           int.Z off = i * 8 * 128 ∧
           o = existT KindInode (bufInode inode_buf0).
Proof.
  rewrite /inode0_map.
  rewrite lookup_gset_to_gmap_Some.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seqZ.
  split.
  - intuition (subst; auto).
    destruct H0 as [y [? ?]]; subst.
    exists y; repeat split; try word.
  - intros.
    destruct H as [i (?&?&?)]; subst.
    split; auto.
    exists i; split; word.
Qed.

Lemma lookup_block0_map (off: u64) o :
  block0_map !! off = Some o ↔
  off = (U64 0) ∧
  o = existT KindBlock (bufBlock block0).
Proof.
  rewrite /block0_map.
  rewrite lookup_singleton_Some.
  intuition auto.
Qed.

Opaque block_bytes.

Lemma bit0_map_not_empty : ∅ ≠ bit0_map.
Proof.
  intro H.
  assert (bit0_map !! (U64 0) = None).
  { rewrite -H. apply lookup_empty. }
  assert (bit0_map !! (U64 0) = Some (existT KindBit (bufBit false))).
  { apply lookup_bit0_map.
    split; auto.
    pose proof block_bytes_pos.
    word. }
  rewrite H0 in H1.
  congruence.
Qed.

Lemma inode0_map_not_empty : ∅ ≠ inode0_map.
Proof.
  intro H. assert (inode0_map !! (U64 0) = None).
  { rewrite -H. apply lookup_empty. }
  apply lookup_gset_to_gmap_None in H0.
  apply H0.
  apply elem_of_list_to_set.
  apply elem_of_list_lookup.
  exists 0%nat; auto.
Qed.

Lemma block0_map_not_empty : ∅ ≠ block0_map.
Proof.
  intro H. assert (block0_map !! (U64 0) = None).
  { rewrite -H. apply lookup_empty. }
  rewrite lookup_singleton in H0. congruence.
Qed.

Hint Resolve bit0_map_not_empty : notempty.
Hint Resolve inode0_map_not_empty : notempty.
Hint Resolve block0_map_not_empty : notempty.

Lemma repeat_lookup_inv {T} (a b : T) : ∀ n i, repeat a n !! i = Some b -> a = b.
Proof.
  induction n; simpl; intros.
  { rewrite lookup_nil in H. congruence. }
  destruct i; eauto.
  inversion H; eauto.
Qed.

Lemma block0_to_vals : Block_to_vals block0 = replicate block_bytes (#(U8 0)).
Proof. reflexivity. Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma extract_inode0 (off: u64) :
  (* off is actually less than 8*8*128 *)
  int.Z off `mod` 1024 = 0 →
  int.Z off < 8*4096 → (* TODO: not sure what bound is *)
  extract_nth block0 inode_bytes (int.nat off `div` (inode_bytes * 8)) =
  inode_to_vals inode_buf0.
Proof.
  intros.
  rewrite /extract_nth.
  rewrite block0_to_vals.
  rewrite take_replicate drop_replicate.
  rewrite /inode_buf0.
  rewrite /inode_to_vals.
  rewrite vec_to_list_replicate.
  rewrite fmap_replicate.
  f_equal.
  rewrite /inode_bytes block_bytes_eq.
  rewrite Nat.min_l; try word.
  change (Z.to_nat 128 * 8)%nat with 1024%nat.
  change (Z.to_nat 4096) with 4096%nat.
  change (Z.to_nat 128) with 128%nat.
  assert (int.nat off < 8 * 4096)%nat by lia.
  cut (int.nat off `div` 1024 < 32)%nat; try lia.
  change (8*4096)%nat with (Z.to_nat 32768) in H1.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z_inj_div.
  lia.
Qed.

Lemma bufDataT_in_block0_bit off o (n: u64) :
  bit0_map !! off = Some o ->
  int.Z n * block_bytes * 8 < 2 ^ 64 ->
  bufDataT_in_block block0 KindBit n off o.
Proof.
  intros H H0.
  eapply lookup_gset_to_gmap_Some in H. intuition subst.
  assert (valid_off KindBit off).
  { apply valid_off_bit_trivial; eauto. }
  rewrite /bufDataT_in_block /=.
  apply elem_of_list_to_set in H1.
  apply elem_of_list_lookup in H1 as [i ?].
  fmap_Some in H1.
  apply lookup_seqZ in H1 as [-> ?].
  intuition eauto.
  + rewrite /is_bufData_at_off. intuition eauto.
    exists (U8 0).
    rewrite !Z.add_0_l.
    split.
    * rewrite /extract_nth block0_to_vals.
      rewrite take_replicate drop_replicate.
      match goal with
      | |- context[replicate ?n _] => replace n with 1%nat; [ reflexivity | ]
      end.
      rewrite block_bytes_eq in H1 |- *.
      rewrite !Nat.mul_1_r.
      rewrite Nat.min_l; [ lia | ].
      replace (int.nat i) with i by word.
      apply Z.div_lt_upper_bound in H1; [ | lia ].
      rewrite -> Z2Nat.id in H1 by lia.
      replace (Nat.div i 8) with (Z.to_nat $ Z.div (Z.of_nat i) 8); try lia.
      rewrite Z2Nat_inj_div; try lia.
      change (Z.to_nat 8) with 8%nat.
      rewrite Nat2Z.id.
      lia.
    * rewrite /get_bit.
      rewrite decide_False //.
      intros Heq%(f_equal int.Z); move: Heq.
      rewrite word.unsigned_and_nowrap.
      rewrite word.unsigned_sru_nowrap.
      { change (int.Z (U8 0)) with 0; simpl.
        rewrite Z.shiftr_0_l //. }
      rewrite /u8_from_u64.
      rewrite word.unsigned_of_Z word.unsigned_modu_nowrap //.
      change (int.Z 8) with 8.
      rewrite block_bytes_eq in H1.
      replace (int.Z i) with (Z.of_nat i) by word.
      rewrite /word.wrap.
      assert (0 ≤ i `mod` 8 < 8) by (apply Z.mod_bound_pos; lia).
      rewrite Z.mod_small; lia.
  + rewrite /valid_addr /addr2flat_z /=.
    rewrite -> block_bytes_eq in *.
    split_and!; try word.
Qed.

Lemma bufDataT_in_block0_inode off o (n: u64) :
  inode0_map !! off = Some o ->
  int.Z n * block_bytes * 8 < 2 ^ 64 ->
  bufDataT_in_block block0 KindInode n off o.
Proof.
  intros.
  eapply lookup_gset_to_gmap_Some in H. intuition subst.
  apply elem_of_list_to_set in H1.
  apply elem_of_list_lookup in H1 as [i Hlookup].
  fmap_Some in Hlookup.
  apply lookup_seqZ in Hlookup as [-> ?].
  rewrite Z.add_0_l.
  set (off:=i * 8* 128).
  rewrite /bufDataT_in_block; simpl.
  rewrite /is_bufData_at_off.
  feed pose proof (extract_inode0 off) as Hextract; [ word .. | ].
  rewrite /valid_addr /valid_off /addr2flat_z /=.
  assert (valid_off KindInode off).
  { rewrite /valid_off /=.
    word. }
  split_and!; auto.
  { rewrite block_bytes_eq. word. }
  - lia.
  - rewrite /valid_off /= in H.
    rewrite block_bytes_eq in H0 |- *.
    word.
Qed.

Ltac Zify.zify_post_hook ::= idtac.

Lemma bufDataT_in_block0_block off o (n: u64) :
  block0_map !! off = Some o ->
  int.Z n * block_bytes * 8 < 2 ^ 64 ->
  bufDataT_in_block block0 KindBlock n off o.
Proof.
  rewrite /block0_map => H H0.
  eapply lookup_singleton_Some in H. intuition subst.
  assert (valid_off KindBlock (U64 0)).
  { rewrite /valid_off.
    replace (int.Z (U64 0)) with 0 by reflexivity.
    rewrite Zmod_0_l. done. }
  rewrite /bufDataT_in_block /=. intuition eauto.
  + rewrite /is_bufData_at_off. intuition eauto.
  + rewrite /valid_addr /addr2flat_z /=.
    intuition try word.
    pose proof (block_bytes_pos). word.
Qed.

Lemma bufDataT_in_block0 kind off o n :
  match kind with
  | KindBit => bit0_map
  | KindInode => inode0_map
  | KindBlock => block0_map
  end !! off = Some o ->
  int.Z n * block_bytes * 8 < 2 ^ 64 ->
  bufDataT_in_block block0 kind n off o.
Proof.
  intros. destruct kind;
          auto using bufDataT_in_block0_bit,
          bufDataT_in_block0_block,
          bufDataT_in_block0_inode.
Qed.

(* sz is the number of blocks besides the log (so the size of the disk - 513) *)
Lemma is_txn_durable_init dinit (kinds: gmap u64 bufDataKind) (sz: nat) :
  dom (gset _) dinit = list_to_set (seqZ 513 sz) →
  dom (gset _) kinds = list_to_set (U64 <$> (seqZ 513 sz)) →
  (513 + Z.of_nat sz) * block_bytes * 8 < 2^64 →
  0 d↦∗ repeat block0 513 ∗ 513 d↦∗ repeat block0 sz -∗
 |==> ∃ γ,
         "%Hγkinds" ∷ ⌜ γ.(invariant.txn_kinds) = kinds ⌝ ∗
         "Htxn_durable" ∷ is_txn_durable γ dinit ∗
         "#Hdurable_lb" ∷ mono_nat_lb_own γ.(txn_walnames).(wal_heap_durable_lb) 0 ∗
         "Hcrashstates" ∷ ghost_var γ.(txn_crashstates) (3/4) (Build_async (kind_heap0 kinds) []) ∗
         "Hmapsto_txns" ∷ ([∗ map] a ↦ o ∈ kind_heap0 kinds, mapsto_txn γ a o).
Proof.
  iIntros (Hdinit_dom Hkinds_dom Hbound) "H".
  iMod (is_wal_inner_durable_init dinit with "H") as (γwalnames) "[Hwal Hwal_res]".
  { len; auto. }

  set (bs:=repeat block0 sz).

  assert (513 + Z.of_nat sz < 2^64) as Hbound2.
  { pose proof (block_bytes_pos). lia. }

  iMod (wal_heap_inv_init γwalnames bs) as (γheapnames Heq1) "Hheap".
  { rewrite /bs; len. }
  iNamed "Hheap".

  iMod (alloc_txn_init_ghost_state γheapnames kinds) as (γ Heq2 Heq3)  "Hinit".
  iNamed "Hinit".
  iMod (ghost_map_insert_big (kind_heap0 kinds) with "logheap") as "[logheap logheap_mapsto_curs]".
  { simpl. apply map_disjoint_empty_r. }
  iMod (ghost_var_update (Build_async (kind_heap0 kinds) [])
          with "crashstates") as "H".
  iEval (rewrite -Qp_quarter_three_quarter) in "H".
  iDestruct (fractional.fractional_split with "H") as "[crashstates1 crashstates2]".

  iMod (alloc_metamap _ (kind_heap0 kinds) with "metaheap") as (metamap) "(metaheap & Hmetas1 & Hmetas2)".

  iModIntro. iExists γ.
  rewrite Heq2.
  iFrame "Hheap_lb crashstates2".
  rewrite /is_txn_durable.
  iSplit.
  { eauto. }
  iSplitR "Hmetas2 logheap_mapsto_curs".
  2: {
    iDestruct (big_sepM2_sepM_1 with "Hmetas2") as "Hmetas2".
    iDestruct (big_sepM_sep with "[$Hmetas2 $logheap_mapsto_curs]") as "H".
    iApply (big_sepM_mono with "H").
    iIntros (k x Hkx) "[H0 H1]".
    iDestruct "H0" as (γm) "(% & Ha & Hb)".
    iExists _. iFrame.
  }
  iExists (log_state0 bs), (Build_async (kind_heap0 kinds) []).
  iExists (Build_async (crash_heap0 bs) []).

  iSplit.
  { iPureIntro.
    auto using log_state0_post_crash. }
  rewrite Heq2 Heq1.
  iFrame "Hwal Hwal_res Hheap_inv wal_heap_locked".
  rewrite /is_txn_state.
  iExists metamap.
  rewrite Heq2.
  simpl. rewrite right_id.
  iFrame "wal_heap_crash_heaps logheap crashstates1 metaheap".

  iSplitL "Hmetas1 wal_heap_h_mapsto".
  - iDestruct (gmap_addr_by_block_big_sepM2 with "Hmetas1") as "Hmetas".
    iDestruct (big_sepM2_dom with "Hmetas") as "%Hmetadom".
    iApply big_sepM_sepM2_merge_ex; eauto.
    iDestruct (big_sepM2_sepM_1 with "Hmetas") as "Hmetas".

    rewrite /kind_heap0 /gmap_addr_by_block.
    rewrite gmap_uncurry_curry_non_empty; last first.
    {
      intros i x Hix. rewrite lookup_fmap in Hix.
      apply fmap_Some_1 in Hix. destruct Hix. intuition idtac.
      destruct x0; subst.
      { eapply bit0_map_not_empty. eassumption. }
      { eapply inode0_map_not_empty. eassumption. }
      { eapply block0_map_not_empty. eassumption. }
    }

    iDestruct (big_sepM_sepM2_merge with "[$wal_heap_h_mapsto $Hmetas]") as "H".
    { rewrite /gh_heapblock0.
      rewrite dom_fmap_L Hkinds_dom.
      rewrite dom_list_to_map_L. f_equal.
      rewrite fst_imap. subst bs. rewrite repeat_length. rewrite /seqZ.
      replace (Z.to_nat (Z.of_nat sz)) with sz by lia.
      rewrite list_fmap_compose. f_equal.
      eapply list_fmap_ext; eauto. lia.
    }

    iDestruct (big_sepM.big_sepM2_sepM_2 with "H") as "H".
    iApply (big_sepM_mono with "H").
    intros.
    iIntros "Hm".
    iDestruct "Hm" as (hb) "(%Hhb & Hmapsto & H)". destruct hb.
    iDestruct "H" as (mm) "(%Hmm & Hmm)".
    iExists _. iSplit; first by eauto.
    rewrite lookup_fmap in H.
    destruct (kinds !! k) eqn:Hk; simpl in H; inversion H; clear H. subst.
    iExists _, _, _. iSplit; first by (subst; eauto).
    iFrame. iApply (big_sepM2_mono with "Hmm").
    intros. iIntros "H".
    iExists _. iFrame. iPureIntro.
    apply lookup_list_to_map_1 in Hhb.
    apply elem_of_lookup_imap_1 in Hhb. destruct Hhb as [hb_i [hb_b [Hhb0 Hhb1]]].
    inversion Hhb0; clear Hhb0; subst. simpl.
    apply repeat_lookup_inv in Hhb1; subst.

    eapply bufDataT_in_block0; eauto.
    assert (is_Some (γ.(txn_kinds) !! U64 (513 + Z.of_nat hb_i))) as Hs; eauto.
    eapply elem_of_dom in Hs. rewrite Hkinds_dom in Hs.
    eapply elem_of_list_to_set in Hs.
    eapply elem_of_list_fmap_2 in Hs. destruct Hs as [y [Hs0 Hs1]]. rewrite Hs0.
    eapply elem_of_seqZ in Hs1. intuition subst.
    replace (int.Z (U64 y)) with y by word.
    rewrite -Z.mul_assoc. rewrite -Z.mul_assoc in Hbound.
    eapply Z.le_lt_trans; last by apply Hbound.
    pose proof (block_bytes_pos).
    eapply Zmult_gt_0_le_compat_r; try lia.

  - rewrite right_id /named.
    rewrite /bufDataTs_in_crashblock.

    rewrite /kind_heap0 /gmap_addr_by_block.
    rewrite gmap_uncurry_curry_non_empty; last first.
    {
      intros i x Hix. rewrite lookup_fmap in Hix.
      apply fmap_Some_1 in Hix. destruct Hix. intuition idtac.
      destruct x0; subst.
      { eapply bit0_map_not_empty. eassumption. }
      { eapply inode0_map_not_empty. eassumption. }
      { eapply block0_map_not_empty. eassumption. }
    }

    iApply big_sepM_sepM2_merge_ex.
    {
      rewrite /crash_heap0.
      rewrite dom_fmap_L Hkinds_dom.
      rewrite dom_list_to_map_L. f_equal.
      rewrite fst_imap. subst bs. rewrite repeat_length. rewrite /seqZ.
      replace (Z.to_nat (Z.of_nat sz)) with sz by lia.
      rewrite -list_fmap_compose.
      eapply list_fmap_ext; eauto.
      intros. rewrite /compose. f_equal. lia.
    }

    rewrite big_sepM_forall. iPureIntro. intros x m Hxm.
    rewrite lookup_fmap in Hxm.
    destruct (kinds !! x) eqn:He; inversion Hxm; clear Hxm; subst.
    exists block0. split.
    {
      rewrite crash_heap0_repeat_block0; last by lia.
      eapply lookup_gset_to_gmap_Some; intuition eauto.
      eapply rangeSet_lookup; try lia.
      assert (is_Some (γ.(txn_kinds) !! x)) as Hs; eauto.
      eapply elem_of_dom in Hs. rewrite Hkinds_dom in Hs.
      eapply elem_of_list_to_set in Hs.
      eapply elem_of_list_fmap_2 in Hs. destruct Hs as [y [Hs0 Hs1]].
      eapply elem_of_seqZ in Hs1. intuition subst; word.
    }

    eexists _. intuition eauto.
    eapply map_Forall_lookup_2. intros.

    eapply bufDataT_in_block0; eauto.
    assert (is_Some (γ.(txn_kinds) !! x)) as Hs; eauto.
    eapply elem_of_dom in Hs. rewrite Hkinds_dom in Hs.
    eapply elem_of_list_to_set in Hs.
    eapply elem_of_list_fmap_2 in Hs. destruct Hs as [y [Hs0 Hs1]].
    eapply elem_of_seqZ in Hs1. intuition subst.
    replace (int.Z (U64 y)) with y by word.
    rewrite -Z.mul_assoc. rewrite -Z.mul_assoc in Hbound.
    etransitivity; last by apply Hbound.
    pose proof (block_bytes_pos).
    eapply Zmult_gt_0_lt_compat_r; lia.
Qed.

Definition crash_heap_match γ logmap walheap : iProp Σ :=
  ([∗ map] blkno ↦ offmap;walblock ∈ gmap_addr_by_block logmap;walheap,
        ∃ blockK,
       "%Htxn_cb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
       "Htxn_in_cb" ∷ bufDataTs_in_crashblock walblock blkno blockK offmap)%I.

Definition crash_heaps_match γ logm crash_heaps : iProp Σ :=
  ([∗ list] logmap;walheap ∈ possible logm;possible crash_heaps, crash_heap_match γ logmap walheap).

Lemma crash_heaps_match_async_take γ logm crash_heaps n :
  (0 < n)%nat →
  (n ≤ length (possible logm))%nat →
  crash_heaps_match γ logm crash_heaps -∗
  crash_heaps_match γ (async_take n logm) (async_take n crash_heaps).
Proof.
  rewrite /crash_heaps_match.
  iIntros (Hlt Hle) "Hl".
  iDestruct (big_sepL2_length with "Hl") as %Hlen.
  iApply (big_sepL2_prefix with "Hl"); auto.
  - apply async_take_possible_prefix; auto.
  - apply async_take_possible_prefix; auto. lia.
  - rewrite ?possible_list_to_async ?take_length; lia.
Qed.

Lemma crash_heaps_match_transfer_gname γ1 γ2 logm crash_heaps :
  txn_kinds γ2 = txn_kinds γ1 →
  crash_heaps_match γ1 logm crash_heaps -∗
  crash_heaps_match γ2 logm crash_heaps.
Proof. iIntros (Heq) "H". rewrite /crash_heaps_match/crash_heap_match Heq. eauto. Qed.

Lemma crash_heaps_match_heapmatch_latest γ logm crash_heaps :
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 ∅ ∗
    "Hcrash_heaps0" ∷ ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
     ⌜hb_latest_update hb = b⌝ ∗
     a ↪[γ.(txn_walnames).(wal_heap_h)] hb) ∗
    "Hcrashheapsmatch" ∷ crash_heaps_match γ logm crash_heaps ==∗
    ∃ metam,
    map_ctx γ.(txn_metaheap) 1 metam ∗
    "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
      ∃ installed bs blockK,
        "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
        "Htxn_hb" ∷ blkno ↪[γ.(txn_walnames).(wal_heap_h)] (HB installed bs) ∗
        "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
    "Hmapsto_txns" ∷ ([∗ map] addr↦bufData ∈ latest logm, ∃ γm, ptsto_mut γ.(txn_metaheap) addr 1 γm ∗ ghost_var γm (1/2) true).
Proof.
  iNamed 1.
  iMod (mapsto_txn_alloc _ logm.(latest) with "Hmetactx") as (metam) "(%Hdom & Hmetactx' & H0 & H1)".

  rewrite /crash_heaps_match /possible.
  rewrite big_sepL2_snoc.
  iDestruct "Hcrashheapsmatch" as "[_ Hlatestmatch]".
  rewrite /crash_heap_match.

  iModIntro. iExists _. iFrame "Hmetactx'".
  iFrame "H0".

  iDestruct (big_sepM2_flip with "Hlatestmatch") as "Hlatestmatch".
  iDestruct (big_sepM2_sepM_merge with "[$Hlatestmatch $Hcrash_heaps0]") as "Hlatestmatch".
  iDestruct (big_sepM2_flip with "Hlatestmatch") as "Hlatestmatch".

  iDestruct (big_sepM2_sepM_1 with "Hlatestmatch") as "Hlatestmatch".
  iDestruct (gmap_addr_by_block_big_sepM with "H1") as "H1".
  iDestruct (big_sepM_sepM2_merge with "[$Hlatestmatch $H1]") as "H".
  { eapply gmap_addr_by_block_dom_eq; eauto. }

  iApply (big_sepM2_mono with "H").
  iIntros (k y1 y2 Hky1 Hky2) "[H0 H1]".
  iDestruct "H0" as (y0) "(%Hcl & H0 & H2)".
  iDestruct "H0" as (block) "[%Hk H0]". iNamed "H0".
  iDestruct "H2" as (hb) "[%Hb Hmapsto]".
  destruct hb.
  iExists _, _, _. iFrame. iFrame "%".

  rewrite /bufDataTs_in_block /bufDataTs_in_crashblock.
  iDestruct (big_sepM_sepM2_merge with "[$Htxn_in_cb $H1]") as "H1".
  { eapply gmap_addr_by_block_dom_eq2; eauto. }

  iApply (big_sepM2_mono with "H1").
  iIntros (k0 y3 y4 Hky3 Hky4) "[%Hblk H]".
  iExists _. iFrame. iPureIntro.
  rewrite -Hb in Hblk. eauto.
Qed.

Global Instance is_txn_always_discretizable γ :
  Discretizable (is_txn_always γ).
Proof. apply _. Qed.

Global Instance is_txn_durable_discretizable γ dinit :
  Discretizable (is_txn_durable γ dinit).
Proof. apply _. Qed.

Lemma log_crash_txns_length ls1 ls2 :
  relation.denote log_crash ls1 ls2 () →
  (length ls2.(log_state.txns) ≤ length ls1.(log_state.txns))%nat.
Proof.
  rewrite log_crash_unfold. intros (?&?&?).
  subst. rewrite /=.
  rewrite -{2}(take_drop (S x) (ls1.(log_state.txns))).
  rewrite app_length. lia.
Qed.

Lemma wal_heap_inv_wf names ls:
  wal_heap_inv names ls -∗
  ⌜ wal_wf ls ⌝.
Proof. iNamed 1. eauto. Qed.

Lemma latest_wal_heap_h_mapsto_split (γ: gname) gh :
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ a ↪[γ] hb) ⊣⊢
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ a ↪[γ]{#1/2} hb) ∗
  ([∗ map] a ↦ b ∈ gh, ∃ hb, ⌜hb_latest_update hb = b⌝ ∗ a ↪[γ]{#1/2} hb).
Proof.
  rewrite -big_sepM_sep.
  repeat f_equiv.
  iSplit.
  - iDestruct 1 as (hb <-) "[H1 H2]".
    iSplitL "H1"; eauto with iFrame.
  - iDestruct 1 as "[H1 H2]".
    iDestruct "H1" as (hb <-) "H1".
    iDestruct "H2" as (hb' <-) "H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %<-.
    iCombine "H1 H2" as "H".
    eauto.
Qed.

(*
Definition txn_pre_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ'.(txn_crashstates) (3/4) σs ∗
              heapspec_durable_exchanger γ.(txn_walnames) (length (possible σs) - 1)).

Definition txn_post_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ.(txn_crashstates) (3/4) σs).

Definition txn_exchanger (γ γ' : @txn_names Σ) : iProp Σ :=
  ∃ ls ls', heapspec_exchanger ls ls' γ.(txn_walnames) γ'.(txn_walnames) ∗
  (txn_pre_exchange γ γ' ∨ txn_post_exchange γ γ').
*)

Definition txn_resources γ γ' logm : iProp Σ :=
  (∃ logm0 (txn_id : nat),
  "%Hasync_pre" ∷ ⌜ async_prefix logm logm0 ⌝ ∗
  "%Hlen_crash_txn" ∷ ⌜ (length (possible logm) = txn_id + 1)%nat ⌝ ∗
  "%Hlen_compare" ∷ ⌜ (length (possible logm) ≤ length (possible logm0))%nat ⌝ ∗
  "Hlogm" ∷ ghost_var γ'.(txn_crashstates) (3/4) logm ∗
  "Holdlogm" ∷ ghost_var γ.(txn_crashstates) (1/4) logm0 ∗
  "Hmapsto_txns" ∷ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ' a v) ∗
  "Hdurable" ∷ mono_nat_lb_own γ'.(txn_walnames).(heapspec.wal_heap_durable_lb) txn_id ∗
  "Hdurable_exchanger" ∷ heapspec_durable_exchanger γ.(txn_walnames) txn_id)%I.


Lemma txn_crash_transform dinit (γ γ': txn_names) γ'_walnames logm1 crash_heaps
 (* (Hwalnames_eq : γ'.(txn_walnames) = γ'_txn_walnames) *)
  (Hkinds_eq : γ'.(txn_kinds) = γ.(txn_kinds)) :
  ("His_txn_always" ∷ is_txn_state γ logm1 crash_heaps ∗
  "Htxn_init" ∷ txn_init_ghost_state γ' ∗
  "Hcrash" ∷ ∃ (σ0 σ' : log_state.t),
             ⌜relation.denote log_crash σ0 σ' tt⌝ ∗
             is_wal_inner_durable γ'_walnames σ' dinit ∗ wal_resources γ'_walnames ∗
             ▷ (wal_heap_inv γ'.(txn_walnames) σ' ∗
                heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) σ0 σ')) -∗
  (|0={∅}=> ∃ (logm' : async (gmap addr object)),
          let γ' := (γ'<|txn_walnames;wal_heap_walnames := γ'_walnames|>) in
         ⌜γ'.(txn_kinds) = γ.(txn_kinds)⌝ ∗ is_txn_durable γ' dinit ∗ txn_resources γ γ' logm').
Proof.
  iNamed 1.
  iDestruct "Hcrash" as (ls1) "HP".
  iDestruct "HP" as (ls2 Hcrashls12) "(Hdur' & Hres' & HP)".
  iNamed "His_txn_always".
  rewrite /txn_resources.

  rewrite /Prec. iDestruct "HP" as "(>Hheap_inv&Hheap_res)".
  rewrite /is_txn_durable.

  rewrite /heapspec_resources.
  iDestruct "Hheap_res" as "(>Hheap_exchanger&>Hlocked_walheap)".
  iDestruct (heapspec_exchange_crash_heaps with "[$] [$]") as "(Hheap_exchange&Hnew)".
  iDestruct "Hnew" as "(Hheap_lb_exchange&Hcrash_heaps0)".
  iNamed "Hcrash_heaps0".

  iDestruct (wal_heap_inv_wf with "Hheap_inv") as %Hls2wf.
  iNamed "Htxn_init".
  iDestruct (big_sepL2_length with "Hcrashheapsmatch") as %Hlen_logm.
  assert (length ls2.(log_state.txns) ≤ length (possible logm1))%nat.
  { rewrite Hlen_logm -Hlenold //=.
    apply log_crash_txns_length. auto. }
  assert (0 < length ls2.(log_state.txns))%nat.
  { destruct Hls2wf. lia. }

  iMod (ghost_var_update (async_take (length ls2.(log_state.txns)) logm1) with "crashstates")
       as "crashstates".
  iDestruct (crash_heaps_match_async_take γ _ _ (length ls2.(log_state.txns)) with "Hcrashheapsmatch")
       as "#Hcrashheapsmatch'"; auto.
  iDestruct (crash_heaps_match_transfer_gname _ γ' with "Hcrashheapsmatch'") as "#Hcrashheapsmatch_new".
  { auto. }

  iMod (ghost_map_insert_big (async_take (length ls2.(log_state.txns)) logm1).(latest) with "logheap")
    as "[logheap Hlatest]".
  { apply map_disjoint_empty_r. }

  iMod (crash_heaps_match_heapmatch_latest γ' with "[$Hcrashheapsmatch_new $metaheap $Hcrash_heaps0]") as
     (metam_new) "(metaheap&Heapmatch_new&Hpts)".

  iExists (async_take (length ls2.(log_state.txns)) logm1).
  iSplitL ""; first eauto.


  iEval (rewrite -Qp_quarter_three_quarter) in "crashstates".
  iDestruct (fractional.fractional_split_1 with "crashstates") as
      "[crashstates1 crashstates2]".
  iDestruct (heapspec_durable_exchanger_dup with "[$]")
            as "(Hheap_lb_exchange1&Hheap_lb_exchange2)".
  iSplitR "Hcrashstates crashstates2 Hheap_lb_exchange2 Hheap_exchange Hpts Hlatest"; last first.
  { iModIntro. iExists _, ((length ls2.(log_state.txns)) - 1)%nat. iFrame.
    iSplitL "".
    {
      iPureIntro. apply async_take_async_prefix; lia.
    }
    iSplitL "".
    { iPureIntro. rewrite /async_take.
      rewrite possible_list_to_async; last first.
      { rewrite take_length. lia. }
      { rewrite take_length. lia. }
    }
    iSplitL "".
    { iPureIntro. rewrite /async_take.
      rewrite possible_list_to_async; last first.
      { rewrite take_length. lia. }
      { rewrite take_length. lia. }
    }
    iCombine "Hpts Hlatest" as "Hpts".
    rewrite -big_sepM_sep.
    iSplitL "Hpts".
    {
      iApply (big_sepM_mono with "Hpts").
      iIntros (???) "(H1&H2)".
      iDestruct "H1" as (γm) "(H1a&H1b)".
      iExists γm. iFrame.
    }
    iNamed "Hheap_exchange". simpl.
    rewrite (wal_post_crash_durable_lb_length_txns ls2); first iFrame "#".
    eapply log_crash_to_post_crash; eauto.
  }
  iExists ls2, _, _. simpl. iFrame "Hheap_inv Hres' Hdur'".

  iFrame "Hcrash_heaps".
  iSplitL "".
  { iModIntro. iPureIntro. eapply log_crash_to_post_crash; eauto. }
  iFrame.
  iExists metam_new.
  iFrame "# ∗".
  simpl. iEval (rewrite right_id) in "logheap". iFrame "logheap".
  eauto.
Qed.

  Definition txn_cfupd_cancel E dinit k γ' : iProp Σ :=
    (<bdisc> (|C={E}_k=> ▷ is_txn_durable γ' dinit)).

Definition txn_cfupd_res E γ γ' : iProp Σ :=
  ⌜γ'.(txn_kinds) = γ.(txn_kinds)⌝ ∗
  (<bdisc> (|C={E}_0=> ▷ ∃ logm, txn_resources γ γ' logm)).

Theorem wpc_MkLog E d dinit (γ:txn_names) k :
  ↑walN ⊆ E →
  ↑invN ⊆ E →
  {{{ is_txn_durable γ dinit }}}
    obj.MkLog (disk_val d) @ k; ⊤
  {{{ γ' (l: loc), RET #l;
      is_txn l γ dinit ∗
      txn_cfupd_cancel E dinit 0 γ' ∗
      txn_cfupd_res E γ γ' }}}
  {{{ ∃ γ' logm', ⌜ txn_kinds γ' = txn_kinds γ ⌝ ∗ is_txn_durable γ' dinit
      ∗ (⌜ γ' = γ ⌝ ∨ txn_resources γ γ' logm') }}}.
Proof.
  iIntros (?? Φ Φc) "Hdur HΦ".
  rewrite /obj.MkLog. wpc_pures.
  { crash_case. iExists _, _. iFrame. eauto. }

  iCache with "Hdur HΦ".
  { crash_case. iExists _, _. iFrame. eauto. }
  wpc_bind (lock.new _).
  wpc_frame; wp_apply (wp_new_free_lock).
  iIntros (lk) "Hlock". iNamed 1.
  wpc_bind (wal.MkLog _).
  iNamed "Hdur".
  iMod (alloc_heapspec_init_ghost_state (γ.(txn_walnames).(wal_heap_walnames)))
         as (γ'_txn_walnames ?) "Hheapspec_init".
  iMod (alloc_txn_init_ghost_state γ'_txn_walnames γ.(txn_kinds)) as
      (γ' Hwalnames_eq Hkinds_eq) "Htxn_init".
  set (P := λ ls, (wal_heap_inv γ.(txn_walnames) ls ∗ heapspec_init_ghost_state γ'_txn_walnames)%I).
  set (Prec (ls ls': log_state.t) :=
         (wal_heap_inv γ'.(txn_walnames) ls' ∗
          heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) ls ls')%I).
  set (Pcrash (ls ls' : log_state.t) := (True)%I : iProp Σ).
  iApply wpc_cfupd.
  wpc_apply (wpc_MkLog_recover dinit P (↑walN) _ _ _ _ Prec Pcrash
            with "[] [$His_wal_inner_durable Hwal_res Hwal_heap_inv Hheapspec_init]").
  - auto.
  - auto.
  - iIntros "!>" (???) ">HP".
    iDestruct "HP" as "[Hinv Hinit]".
    iMod (wal_heap_inv_crash_transform with "Hinv Hinit") as "[Hinv Hres]"; eauto.
    rewrite /Prec /Pcrash.
    rewrite Hwalnames_eq.
    iModIntro.
    by iFrame.
  - iFrame.
  - iSplit.
    { iLeft in "HΦ".
      iIntros "Hcrash HC".
      iDestruct "Hcrash" as (γ'wal_names) "Hcrash".
      iPoseProof (txn_crash_transform with "[$]") as "Htransform".
      { auto. }
      iDestruct (fupd_level_le _ _ _ k with "Htransform") as "Htransform".
      { lia. }
      iApply fupd_level_fupd.
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      iModIntro. iApply "HΦ".
      iDestruct "Htransform" as (?) "(?&?&?)".
      iExists _, _. iFrame.
    }
    iNext. iIntros (γ'' l) "(#Hwal & Hwal_cfupd & #Hwal_cinv)".
    iApply wpc_fupd.
    iApply wpc_cfupd.
    wpc_frame_compl "Hlock Hlocked_walheap".
    {
      iLeft in "HΦ".
      iIntros "HC".
      rewrite /wal_cfupd_cancel.
      rewrite own_discrete_elim.
      iSpecialize ("Hwal_cfupd" with "[$]").
      iMod (fupd_mask_mono with "Hwal_cfupd") as "Hwal_cfupd"; auto.
      iPoseProof (txn_crash_transform with "[$His_txn_always $Htxn_init Hwal_cfupd]") as "Htransform".
      { auto. }
      { iDestruct "Hwal_cfupd" as (??) "H".
        iExists _, _. iFrame.
      }
      iApply fupd_level_fupd.
      iDestruct (fupd_level_le _ _ _ k with "Htransform") as "Htransform".
      { lia. }
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      iModIntro. iApply "HΦ".
      iDestruct "Htransform" as (?) "(?&?&?)".
      iExists _, _. iFrame.
    }
    rewrite -wp_fupd.
    wp_apply wp_allocStruct; first by val_ty.
    iIntros (txn_l) "Htxn".
    iApply struct_fields_split in "Htxn". iNamed "Htxn".
    wp_pures.
    iMod (readonly_alloc_1 with "mu") as "#mu".
    iMod (readonly_alloc_1 with "log") as "#log".
    iMod (alloc_lock lockN _ _ (is_txn_locked txn_l γ.(txn_walnames))
            with "Hlock [pos Hlocked_walheap]") as "#Htxn_lock".
    { iNext. rewrite /is_txn_locked.
      iExists _, _, _; iFrame. }
    iModIntro.
    iNamed 1.
    rewrite /wal_cfupd_cancel.
    iDestruct (own_discrete_laterable with "Hwal_cfupd") as (Pwal_tok) "(HPwal_tok&#HPwal_tok_wand)".
    iMod (ncinv_cinv_alloc' invN _ _ E
            (is_txn_always γ ∗ Pwal_tok ∗ txn_init_ghost_state γ')
            (∃ logm',
                txn_resources γ ((γ' <| txn_walnames; wal_heap_walnames := γ'' |>)) logm')%I
            (is_txn_durable ((γ' <| txn_walnames; wal_heap_walnames := γ'' |>)) dinit)%I
      with "[] [His_txn_always HPwal_tok Htxn_init]") as "(#Htxn_inv&Hcfupd)".
    { set_solver. }
    { iIntros "!> (>H&?&>Hinit) #HC".
      iSpecialize ("Hwal_cinv" with "[$]").
      iMod ("HPwal_tok_wand" with "[$]") as "Hwal_cfupd".
      iSpecialize ("Hwal_cfupd" with "HC").
      iDestruct "H" as (??) "H".
      iMod (fupd_mask_mono with "Hwal_cfupd") as "Hwal_cfupd".
      { solve_ndisj. }
      iPoseProof (txn_crash_transform _ γ γ' with "[H Hwal_cfupd Hinit]") as "Htransform".
      { auto. }
      { iFrame "H Hinit".
        iDestruct "Hwal_cfupd" as (??) "(?&?&?&?)".
        iExists _, _. iFrame.
      }
      iApply fupd_level_fupd.
      iMod (fupd_level_mask_mono with "Htransform") as "Htransform"; auto.
      { set_solver+. }
      iModIntro.
      iDestruct "Htransform" as (??) "(Hdur&Hres)".
      iSplitR "Hdur".
      { iNext. iExists _. iFrame. }
      { iNext. iFrame. }
    }
    { iNext. iFrame. iExists _, _; iFrame. }
    iDestruct "Hcfupd" as "(Hcfupd_cancel&Hcfupd)".
    iRight in "HΦ".
    iApply "HΦ".
    iSplitL "".
    {
      iExists _, _; iFrame "#".
      iSplitL.
      - iApply (is_wal_alter with "Hwal").
        do 2 iModIntro. iClear "#".
        rewrite /P.
        iIntros (?) "[$ $]".
        iIntros (?) "$".
      -  iApply (ncinv_alter with "Htxn_inv").
         iIntros "!> !> !> (H&?)".
         iFrame. eauto.
    }
    iModIntro. iFrame "Hcfupd_cancel".
    rewrite /txn_cfupd_res.
    rewrite /txn_cfupd_cancel.
    iFrame.
    Unshelve.
    (* XXX: track this down. *)
    { simpl. eauto. }
    { exact (Build_async (∅: gmap addr object) []). }
    { exact (Build_async (∅: gmap addr object) []). }
    { exact (U64 0). }
Qed.

End goose_lang.

Section stable.
Context `{!txnG Σ}.
Context `{!heapGS Σ}.

Existing Instance ghost_var_into_crash.
Existing Instance mono_nat_auth_own_into_crash.
Existing Instance is_wal_inner_durable_stable.

Global Instance is_txn_durable_stable γ dinit:
  IntoCrash (is_txn_durable γ dinit) (λ _, is_txn_durable γ dinit).
Proof.
  rewrite /IntoCrash.
  iNamed 1.
  iDestruct (post_crash_nodep with "His_txn_always") as "His_txn_always".
  iDestruct (post_crash_nodep with "Hwal_res") as "Hwal_res".
  iDestruct (post_crash_nodep with "Hwal_heap_inv") as "Hwal_heap_inv".
  iDestruct (post_crash_nodep with "Hlocked_walheap") as "Hlocked_walheap".
  iCrash.
  iExists ls', logm, crash_heaps.
  iSplit; first eauto.
  iFrame "Hwal_res".
  iFrame "Hwal_heap_inv".
  iFrame "Hlocked_walheap".
  iFrame "His_txn_always".
  eauto.
Qed.
End stable.
