From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import addr.

Set Implicit Arguments.

Definition addr : Type := u64 * u64.

Definition addrBlock (a : addr) := fst a.
Definition addrOff (a : addr) := snd a.
Definition Build_addr b o : addr := (b, o).

Notation "a '.(addrBlock)'" := (addrBlock a) (at level 0, only parsing).
Notation "a '.(addrOff)'" := (addrOff a) (at level 0, only parsing).

Remove Hints finite.finite_countable : typeclass_instances.

Definition addr2val (a : addr) : val :=
  (#a.(addrBlock), (#a.(addrOff), #())).

Definition addr2flat_z (a : addr) : Z :=
  int.val a.(addrBlock) * block_bytes * 8 + int.val a.(addrOff).

Definition addr2flat (a : addr) : u64 :=
  addr2flat_z a.

Definition valid_addr (a : addr) : Prop :=
  int.val a.(addrOff) < block_bytes*8 ∧
  int.val a.(addrBlock) * block_bytes < 2^64 ∧
  int.val a.(addrBlock) * block_bytes * 8 < 2^64 ∧
  addr2flat_z a < 2^64.

Theorem addr2flat_z_eq `(valid_addr a0) `(valid_addr a1) :
  addr2flat a0 = addr2flat a1 →
  addr2flat_z a0 = addr2flat_z a1.
Proof.
  destruct a0, a1.
  unfold addr2flat, valid_addr, addr2flat_z, block_bytes in *.
  simpl in *; intuition.
  apply (f_equal int.val) in H.
  revert H.
  word.
Qed.

Theorem addr2flat_eq `(valid_addr a0) `(valid_addr a1) :
  addr2flat a0 = addr2flat a1 →
  a0 = a1.
Proof.
  intros.
  eapply addr2flat_z_eq in H; eauto.
  destruct a0, a1.
  unfold valid_addr, addr2flat_z, block_bytes in *.
  simpl in *.
  intuition.
  replace u0 with u2 in *.
  { replace u with u1; auto.
    assert (int.val u * Z.to_nat 4096 * 8 = int.val u1 * Z.to_nat 4096 * 8) by lia.
    word.
  }
  word.
Qed.

Theorem addr2flat_ne `(valid_addr a0) `(valid_addr a1) :
  a0 ≠ a1 ->
  addr2flat a0 ≠ addr2flat a1.
Proof.
  intros; intuition.
  apply H.
  eapply addr2flat_eq; eauto.
Qed.


Section flatid2addr.

  Variable (T : Type).

  Definition flatid_addr_map (fm : gmap u64 T) (am : gmap addr T) : Prop :=
    ( ∀ a v, am !! a = Some v -> valid_addr a ∧ fm !! (addr2flat a) = Some v ) ∧
    ( ∀ fa v, fm !! fa = Some v -> ∃ a, valid_addr a ∧ addr2flat a = fa ∧ am !! a = Some v ).

  Theorem flatid_addr_lookup fm am a :
    flatid_addr_map fm am ->
    valid_addr a ->
    fm !! (addr2flat a) = am !! a.
  Proof.
    unfold flatid_addr_map; intros.
    destruct (am !! a) eqn:Heq.
    - apply H; eauto.
    - destruct (fm !! addr2flat a) eqn:Heq2; eauto.
      apply H in Heq2; eauto.
      destruct Heq2; intuition idtac.
      apply addr2flat_eq in H1; eauto; subst.
      congruence.
  Qed.

  Theorem flatid_addr_lookup_valid fm am a :
    flatid_addr_map fm am ->
    is_Some (am !! a) ->
    valid_addr a.
  Proof.
    unfold flatid_addr_map; intros.
    destruct H0. apply H in H0. intuition eauto.
  Qed.

  Theorem flatid_addr_insert fm am a v :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (<[addr2flat a := v]> fm) (<[a := v]> am).
  Proof.
    rewrite /flatid_addr_map; split; intros.
    - destruct (decide (a = a0)); subst.
      + rewrite lookup_insert in H1; inversion H1; clear H1; subst.
        repeat rewrite -> lookup_insert; eauto.
      + rewrite -> lookup_insert_ne in H1 by eauto.
        apply H in H1; intuition eauto.
        rewrite -> lookup_insert_ne by (apply addr2flat_ne; eauto).
        eauto.
    - destruct (decide (addr2flat a = fa)); subst.
      + rewrite lookup_insert in H1; inversion H1; clear H1; subst.
        eexists.
        repeat rewrite -> lookup_insert; eauto.
      + rewrite -> lookup_insert_ne in H1 by eauto.
        apply H in H1; destruct H1. intuition eauto.
        exists x; intuition eauto.
        rewrite -> lookup_insert_ne; eauto.
        congruence.
  Qed.

  Theorem flatid_addr_insert_inv_2 fm am a v :
    flatid_addr_map fm (<[a := v]> am) ->
      valid_addr a ∧
      fm !! (addr2flat a) = Some v ∧
      flatid_addr_map (delete (addr2flat a) fm) (delete a am).
  Proof.
    intros.
    destruct H.
    edestruct H.
    { erewrite lookup_insert; eauto. }
    intuition eauto.
    split; intros.
    - destruct (decide (a = a0)); subst.
      { rewrite lookup_delete in H3; congruence. }
      rewrite lookup_delete_ne in H3; eauto.
      edestruct H.
      { rewrite lookup_insert_ne; eauto. }
      intuition eauto.
      rewrite lookup_delete_ne; eauto.
      eapply addr2flat_ne; eauto.
    - destruct (decide (addr2flat a = fa)); subst.
      { rewrite lookup_delete in H3; congruence. }
      rewrite lookup_delete_ne in H3; eauto.
      apply H0 in H3. destruct H3.
      exists x. intuition eauto.
      rewrite -> lookup_insert_ne in H6 by congruence.
      rewrite -> lookup_delete_ne by congruence.
      eauto.
  Qed.

  Theorem flatid_addr_insert_inv_1 fm am fa v :
    flatid_addr_map (<[fa := v]> fm) am ->
    ∃ a,
      valid_addr a ∧
      fa = addr2flat a ∧
      am !! a = Some v ∧
      flatid_addr_map (delete fa fm) (delete a am).
  Proof.
    intros.
    destruct H.
    edestruct H0.
    { erewrite lookup_insert; eauto. }
    exists x.
    intuition eauto.
    split; intros.
    - destruct (decide (a = x)); subst.
      { rewrite lookup_delete in H3; congruence. }
      rewrite lookup_delete_ne in H3; eauto.
      edestruct H; eauto.
      intuition eauto.
      rewrite -> lookup_insert_ne in H5 by (apply addr2flat_ne; eauto).
      rewrite lookup_delete_ne; eauto.
      eapply addr2flat_ne; eauto.
    - destruct (decide (fa = fa0)); subst.
      { rewrite lookup_delete in H3; congruence. }
      rewrite lookup_delete_ne in H3; eauto.
      edestruct H0.
      { rewrite lookup_insert_ne; eauto. }
      exists x0; intuition eauto.
      rewrite -> lookup_delete_ne by congruence.
      eauto.
  Qed.

  Theorem flatid_addr_delete fm am a :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (delete (addr2flat a) fm) (delete a am).
  Proof.
    rewrite /flatid_addr_map; split; intros.
    - destruct (decide (a = a0)); subst.
      + rewrite lookup_delete in H1; congruence.
      + rewrite -> lookup_delete_ne in H1 by eauto.
        apply H in H1; intuition eauto.
        rewrite -> lookup_delete_ne by (apply addr2flat_ne; eauto).
        eauto.
    - destruct (decide (addr2flat a = fa)); subst.
      + rewrite lookup_delete in H1; congruence.
      + rewrite -> lookup_delete_ne in H1 by eauto.
        apply H in H1; destruct H1.
        exists x; intuition eauto.
        rewrite lookup_delete_ne; eauto.
        congruence.
  Qed.

  Theorem flatid_addr_empty :
    flatid_addr_map ∅ ∅.
  Proof.
    unfold flatid_addr_map; split; intros.
    - rewrite lookup_empty in H; congruence.
    - rewrite lookup_empty in H; congruence.
  Qed.

  Theorem flatid_addr_empty_1 m :
    flatid_addr_map ∅ m -> m = ∅.
  Proof.
    unfold flatid_addr_map; intros.
    apply map_empty; intros.
    destruct (m !! i) eqn:He; eauto.
    apply H in He. rewrite lookup_empty in He. intuition congruence.
  Qed.

  Theorem flatid_addr_empty_2 m :
    flatid_addr_map m ∅ -> m = ∅.
  Proof.
    unfold flatid_addr_map; intros.
    apply map_empty; intros.
    destruct (m !! i) eqn:He; eauto.
    apply H in He. destruct He. rewrite lookup_empty in H0. intuition congruence.
  Qed.

End flatid2addr.


Section map.
  Context {PROP : bi}.
  Context `{Countable K} {A : Type}.

  Theorem big_sepM_flatid_addr_map_1 (Φ : _ -> A -> PROP) fm am :
    flatid_addr_map fm am ->
    ([∗ map] a↦b ∈ am, Φ a b) -∗ [∗ map] fa↦b ∈ fm, ∃ a, ⌜ fa = addr2flat a ⌝ ∗ Φ a b.
  Proof.
    rewrite <- (list_to_map_to_list am).
    pose proof (NoDup_fst_map_to_list am); revert H0.
    generalize (map_to_list am); intros l H0.
    clear am; intros.
    iIntros "H".

    iInduction l as [|] "IH" forall (fm H0 H1).
    - simpl in *. apply flatid_addr_empty_2 in H1. rewrite H1.
      repeat rewrite big_sepM_empty. done.
    - simpl in *. inversion H0; clear H0; subst.
      apply flatid_addr_insert_inv_2 in H1; intuition idtac.
      iDestruct (big_sepM_insert_delete with "H") as "[Ha H]".
      erewrite <- (insert_id fm) by eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Ha".
      { iExists _; iFrame. done. }
      rewrite delete_notin.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      rewrite -> (delete_notin (list_to_map _)) in H3.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("IH" $! _ H5 H3 with "H") as "H".
      iFrame.
  Qed.

  Theorem big_sepM_flatid_addr_map_2 (Φ : _ -> A -> PROP) fm am :
    flatid_addr_map fm am ->
    ([∗ map] fa↦b ∈ fm, Φ fa b) -∗ [∗ map] a↦b ∈ am, Φ (addr2flat a) b.
  Proof.
    rewrite <- (list_to_map_to_list fm).
    pose proof (NoDup_fst_map_to_list fm); revert H0.
    generalize (map_to_list fm); intros l H0.
    clear fm; intros.
    iIntros "H".

    iInduction l as [|] "IH" forall (am H0 H1).
    - simpl in *. apply flatid_addr_empty_1 in H1. rewrite H1.
      repeat rewrite big_sepM_empty. done.
    - simpl in *. inversion H0; clear H0; subst.
      apply flatid_addr_insert_inv_1 in H1; destruct H1; intuition subst.
      iDestruct (big_sepM_insert_delete with "H") as "[Ha H]".
      erewrite <- (insert_id am) by eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Ha".
      { rewrite H0. iFrame. }
      rewrite delete_notin.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      rewrite -> (delete_notin (list_to_map _)) in H6.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("IH" $! _ H5 H6 with "H") as "H".
      iFrame.
  Qed.

End map.


Section gmap_curry.

  Context `{EqDecision A} `{Countable A}.
  Context `{EqDecision B} `{Countable B}.
  Variable (T : Type).

  Theorem gmap_uncurry_insert (m : gmap (A * B) T) (k : A * B) (v : T) :
    m !! k = None ->
    gmap_uncurry (<[k:=v]> m) =
      <[fst k :=
        <[snd k := v]> (default ∅ ((gmap_uncurry m) !! fst k))]>
      (gmap_uncurry m).
  Proof.
    intros.
    destruct k as [b o].
    rewrite /gmap_uncurry.
    rewrite map_fold_insert_L; eauto.
    2: {
      intros.
      destruct j1, j2.
      destruct (decide (a = a0)); subst.
      - repeat rewrite <- partial_alter_compose.
        apply partial_alter_ext.
        destruct x; intros; simpl.
        + rewrite insert_commute; eauto. congruence.
        + rewrite insert_commute; eauto. congruence.
      - rewrite partial_alter_commute; eauto.
    }

    simpl.
    eapply partial_alter_ext; intros.
    rewrite H2. reflexivity.
  Qed.

  Theorem gmap_uncurry_lookup_exists (m : gmap (A * B) T) (k : A * B) (v : T) :
    m !! k = Some v ->
    ∃ offmap,
      gmap_uncurry m !! (fst k) = Some offmap ∧
      offmap !! (snd k) = Some v.
  Proof.
    intros.
    destruct k.
    destruct (gmap_uncurry m !! a) eqn:He.
    - eexists; intuition eauto.
      rewrite -lookup_gmap_uncurry in H1.
      rewrite He in H1; simpl in H1. eauto.
    - exfalso. simpl in He.
      pose proof (lookup_gmap_uncurry_None m a). destruct H2.
      rewrite H2 in H1; eauto. congruence.
  Qed.

End gmap_curry.


Section gmap_addr_by_block.

  Variable (T : Type).

  Definition gmap_addr_by_block (m : gmap addr T) : gmap u64 (gmap u64 T) :=
    gmap_uncurry m.

  Theorem gmap_addr_by_block_empty :
    gmap_addr_by_block ∅ = ∅.
  Proof.
    rewrite /gmap_addr_by_block /gmap_uncurry.
    apply map_fold_empty.
  Qed.

  Theorem gmap_addr_by_block_insert (m : gmap addr T) (a : addr) (v : T) :
    m !! a = None ->
    gmap_addr_by_block (<[a:=v]> m) =
      <[a.(addrBlock) :=
        <[a.(addrOff) := v]> (default ∅ ((gmap_addr_by_block m) !! a.(addrBlock)))]>
      (gmap_addr_by_block m).
  Proof.
    intros.
    destruct a as [b o].
    rewrite /gmap_addr_by_block.
    rewrite gmap_uncurry_insert; eauto.
  Qed.

  Theorem gmap_addr_by_block_filter (m : gmap addr T) (P : u64 -> Prop)
      `{! ∀ blkno, Decision (P blkno)} :
    gmap_addr_by_block (filter (λ x, P (fst x).(addrBlock)) m) =
    filter (λ x, P (fst x)) (gmap_addr_by_block m).
  Proof.
    induction m using map_ind.
    - rewrite /gmap_addr_by_block /gmap_uncurry.
      rewrite map_filter_empty.
      rewrite map_fold_empty.
      rewrite map_filter_empty. eauto.
    - destruct i as [b o].
      rewrite gmap_addr_by_block_insert; eauto; simpl.
      destruct (decide (P b)).
      2: {
        rewrite map_filter_insert_not; eauto.
        rewrite map_filter_insert_not; eauto.
      }

      rewrite map_filter_insert; eauto.
      rewrite map_filter_insert; eauto.
      rewrite -IHm; clear IHm.
      rewrite gmap_addr_by_block_insert; eauto; simpl.
      2: { rewrite map_filter_lookup_None; eauto. }

      f_equal. f_equal. f_equal.
      rewrite /gmap_addr_by_block.

      clear H0.
      induction m using map_ind.
      + rewrite map_filter_empty. eauto.
      + destruct (decide (P (addrBlock i))).
        * rewrite map_filter_insert; eauto.
          repeat rewrite gmap_uncurry_insert; eauto.
          2: rewrite map_filter_lookup_None; eauto.
          destruct (decide (i.1 = b)); subst.
          { repeat rewrite lookup_insert. f_equal. f_equal. rewrite IHm. eauto. }
          repeat rewrite lookup_insert_ne; eauto.
        * rewrite map_filter_insert_not; eauto. rewrite IHm.
          rewrite gmap_uncurry_insert; eauto.
          destruct (decide (i.1 = b)); subst.
          { exfalso. apply n. eauto. }
          rewrite lookup_insert_ne; eauto.
  Qed.

  Theorem gmap_addr_by_block_off_not_empty (m : gmap addr T) (blkno : u64) (offmap : gmap u64 T) :
    gmap_addr_by_block m !! blkno = Some offmap ->
    offmap ≠ ∅.
  Proof.
    intros. eapply gmap_uncurry_non_empty. eauto.
  Qed.

  Theorem gmap_addr_by_block_lookup (m : gmap addr T) (a : addr) (v : T) :
    m !! a = Some v ->
    ∃ offmap,
      gmap_addr_by_block m !! a.(addrBlock) = Some offmap ∧
      offmap !! a.(addrOff) = Some v.
  Proof.
    intros.
    rewrite /gmap_addr_by_block.
    apply gmap_uncurry_lookup_exists. eauto.
  Qed.


  Context {PROP : bi}.

  Theorem gmap_addr_by_block_big_sepM (m : gmap addr T) (Φ : addr -> T -> PROP) :
    ( [∗ map] a ↦ v ∈ m, Φ a v ) -∗
    ( [∗ map] blkno ↦ offmap ∈ gmap_addr_by_block m,
        [∗ map] off ↦ v ∈ offmap, Φ (Build_addr blkno off) v ).
  Proof.
    iIntros "Hm".
    iInduction m as [|i x m] "IH" using map_ind.
    - rewrite gmap_addr_by_block_empty. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct ("IH" with "Hm") as "Hm".
      rewrite gmap_addr_by_block_insert; eauto.
      destruct i as [b o].
      destruct (gmap_addr_by_block m !! b) eqn:He.
      + iDestruct (big_sepM_insert_acc with "Hm") as "[Hb Hm]"; eauto.
        iApply "Hm".
        iApply big_sepM_insert.
        { simpl.
          pose proof (lookup_gmap_uncurry m b o).
          rewrite H in H0. rewrite He in H0. simpl in H0.
          rewrite He. simpl. eauto. }
        rewrite He. iFrame.
      + iApply big_sepM_insert; eauto.
        iFrame.
        rewrite He /=.
        iApply big_sepM_insert; eauto. iFrame.
        iApply big_sepM_empty. done.
  Qed.

  Theorem gmap_addr_by_block_big_sepM' (m : gmap addr T) (Φ : addr -> T -> PROP) :
    ( [∗ map] blkno ↦ offmap ∈ gmap_addr_by_block m,
        [∗ map] off ↦ v ∈ offmap, Φ (Build_addr blkno off) v ) -∗
    ( [∗ map] a ↦ v ∈ m, Φ a v ).
  Proof.
    iIntros "Hm".
    rewrite /gmap_addr_by_block.
    iInduction m as [|i x m] "IH" using map_ind.
    - iApply big_sepM_empty. done.
    - destruct i as [i0 i1].
      rewrite gmap_uncurry_insert; eauto; simpl.
      destruct (gmap_uncurry m !! i0) eqn:He.
      + iDestruct (big_sepM_insert_delete with "Hm") as "[Hi0 Hm]"; simpl.
        iDestruct (big_sepM_insert with "Hi0") as "[Hi1 Hi0]".
        { rewrite -lookup_gmap_uncurry in H. rewrite He /= in H. done. }
        iApply big_sepM_insert; eauto. iFrame.
        iDestruct (big_sepM_insert_delete with "[$Hm $Hi0]") as "Hm".
        rewrite insert_id; eauto.
        iApply "IH"; iFrame.
      + iDestruct (big_sepM_insert with "Hm") as "[Hi0 Hm]"; eauto; simpl.
        iDestruct (big_sepM_insert with "Hi0") as "[Hi1 _]".
        { rewrite lookup_empty; eauto. }
        iApply big_sepM_insert; eauto. iFrame.
        iApply "IH". iFrame.
  Qed.

  Theorem gmap_addr_by_block_dom_union (m0 m1 : gmap addr T) :
    dom (gset u64) (gmap_addr_by_block (m0 ∪ m1)) =
    dom (gset u64) (gmap_addr_by_block m0) ∪
    dom (gset u64) (gmap_addr_by_block m1).
  Proof.
    rewrite /gmap_addr_by_block.
    eapply elem_of_equiv_L; split; intros.
    - destruct (decide (x ∈ dom (gset u64) (gmap_uncurry m0))); try set_solver.
      destruct (decide (x ∈ dom (gset u64) (gmap_uncurry m1))); try set_solver.
      exfalso.
      assert (x ∉ dom (gset u64) (gmap_uncurry (m0 ∪ m1))); try set_solver.

      apply not_elem_of_dom in n.
      apply not_elem_of_dom in n0.
      apply not_elem_of_dom.

      erewrite lookup_gmap_uncurry_None in n.
      erewrite lookup_gmap_uncurry_None in n0.
      erewrite lookup_gmap_uncurry_None; intros j.
      specialize (n j). specialize (n0 j).
      eapply lookup_union_None; eauto.

    - destruct (decide (x ∈ dom (gset u64) (gmap_uncurry (m0 ∪ m1)))); try set_solver.
      exfalso.
      assert (x ∉ dom (gset u64) (gmap_uncurry m0) ∪ dom (gset u64) (gmap_uncurry m1)); try set_solver.
      apply not_elem_of_dom in n.
      apply not_elem_of_union; split; apply not_elem_of_dom.

      + erewrite lookup_gmap_uncurry_None; intros j.
        erewrite lookup_gmap_uncurry_None in n.
        specialize (n j).
        eapply lookup_union_None in n. intuition. 

      + erewrite lookup_gmap_uncurry_None; intros j.
        erewrite lookup_gmap_uncurry_None in n.
        specialize (n j).
        eapply lookup_union_None in n. intuition.
  Qed.

  Lemma gmap_addr_by_block_union_lookup (m0 m1 : gmap addr T) o0 o1 k :
    gmap_addr_by_block m0 !! k = Some o0 ->
    gmap_addr_by_block m1 !! k = Some o1 ->
    gmap_addr_by_block (m0 ∪ m1) !! k = Some (o0 ∪ o1).
  Proof.
    rewrite /gmap_addr_by_block.
    intros.
    eapply gmap_uncurry_non_empty in H as H'.
    eapply map_choose in H'. destruct H' as [i [x H']].
    assert (m0 !! (k, i) = Some x).
    { rewrite -(lookup_gmap_uncurry m0). rewrite H. eauto. }
    assert ((m0 ∪ m1) !! (k, i) = Some x).
    { eapply lookup_union_Some_l; eauto. }
    eapply gmap_uncurry_lookup_exists in H2 as H2'.
    destruct H2' as [offmap [H2' H2'']].
    simpl in *.
    rewrite H2'. f_equal.
    apply map_eq; intros j.
    destruct ((m0 ∪ m1) !! (k, j)) eqn:He.
    all: pose proof He as He'.
    all: rewrite -lookup_gmap_uncurry H2' /= in He'.
    all: rewrite He'; symmetry.
    2: {
      eapply lookup_union_None in He; intuition.
      rewrite -lookup_gmap_uncurry H /= in H3.
      rewrite -lookup_gmap_uncurry H0 /= in H4.
      eapply lookup_union_None; eauto.
    }
    eapply lookup_union_Some_raw in He; intuition.
    { rewrite -lookup_gmap_uncurry H /= in H3. eapply lookup_union_Some_l; eauto. }
    { rewrite -lookup_gmap_uncurry H /= in H4. rewrite -lookup_gmap_uncurry H0 /= in H5.
      eapply lookup_union_Some_raw; eauto. }
  Qed.

End gmap_addr_by_block.


Theorem gmap_addr_by_block_fmap {A B} (m : gmap addr A) (f : A -> B) :
  gmap_addr_by_block (f <$> m) =
    (λ (bm : gmap _ _), f <$> bm) <$> (gmap_addr_by_block m).
Proof.
  rewrite /gmap_addr_by_block.
  apply map_eq; intros.
  rewrite lookup_fmap.
  destruct (gmap_uncurry m !! i) eqn:He; simpl.
  - destruct (gmap_uncurry (f <$> m) !! i) eqn:Hee.
    2: {
      eapply gmap_uncurry_non_empty in He as He'.
      apply map_choose in He'. destruct He' as [j' [x' He']].
      erewrite lookup_gmap_uncurry_None in Hee.
      specialize (Hee j'). rewrite lookup_fmap in Hee.
      rewrite -lookup_gmap_uncurry He /= He' /= in Hee.
      congruence.
    }
    rewrite Hee.
    f_equal.
    apply map_eq; intros.

    replace (g0 !! i0) with ((f <$> m) !! (i, i0)).
    2: { rewrite -lookup_gmap_uncurry Hee /=. done. }

    rewrite ?lookup_fmap.
    replace (g !! i0) with (m !! (i, i0)).
    2: { rewrite -lookup_gmap_uncurry He /=. done. }
    done.

  - erewrite lookup_gmap_uncurry_None in He.
    erewrite lookup_gmap_uncurry_None. intros j. specialize (He j).
    rewrite lookup_fmap. rewrite He. done.
Qed.


Section heap.
Context `{!heapG Σ}.

Hint Unfold block_bytes : word.
Hint Unfold valid_addr : word.
Hint Unfold addr2flat : word.
Hint Unfold addr2flat_z : word.

Theorem wp_Addr__Flatid a :
  {{{
    ⌜ valid_addr a ⌝
  }}}
    Addr__Flatid (addr2val a)
  {{{
    v, RET #v; ⌜ v = addr2flat a ⌝
  }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  iApply "HΦ".
  iPureIntro.

  word_cleanup.
  rewrite ?word.unsigned_mul. (* XXX why is this needed? *)
  word_cleanup.
Qed.

End heap.
