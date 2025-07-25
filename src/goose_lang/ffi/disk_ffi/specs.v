From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import ectx_lifting.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting.
From Perennial.goose_lang Require Import crash_modality.

From Perennial.goose_lang.ffi.disk_ffi Require Import impl.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

Class diskGS Σ : Set := DiskGS
  { #[global] diskG_gen_heapG :: gen_heap.gen_heapGS Z Block Σ; }.


Class disk_preG Σ : Set :=
  { #[global] disk_preG_gen_heapG :: gen_heap.gen_heapGpreS Z Block Σ; }.

Definition diskΣ : gFunctors :=
  #[gen_heapΣ Z Block].

#[global]
Instance subG_diskG Σ : subG diskΣ Σ → disk_preG Σ.
Proof. solve_inG. Qed.

Definition disk_update_pre {Σ} (dG: disk_preG Σ) (n: gen_heap_names) :=
  {| diskG_gen_heapG := gen_heapG_update_pre (@disk_preG_gen_heapG _ dG) n |}.

Section disk.
  #[local] Existing Instances disk_op disk_model disk_semantics.

  Program Instance disk_interp: ffi_interp disk_model :=
    {| ffiLocalGS := diskGS;
       ffiGlobalGS _ := ()%type;
       ffi_local_ctx Σ _ (d: @ffi_state disk_model) := gen_heap.gen_heap_interp d;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ _ (d: @ffi_state disk_model) :=
                      ([∗ map] l↦v ∈ d, (gen_heap.pointsto (L:=Z) (V:=Block) l (DfracOwn 1) v))%I;
       ffi_global_start _ _ _ := True%I;
       ffi_restart := fun _ _ (d: @ffi_state disk_model) => True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := ⌜ hF1 = hF2 ∧ σ1 = σ2 ⌝%I;
    |}.

  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
  Instance goose_diskGS : diskGS Σ := goose_ffiLocalGS.

  Notation "l d↦{ dq } v" := (gen_heap.pointsto (L:=Z) (V:=Block) l dq v%V)
                             (at level 20, dq at level 50, format "l  d↦{ dq }  v") : bi_scope.
  Notation "l d↦{# q } v" := (gen_heap.pointsto (L:=Z) (V:=Block) l (DfracOwn q) v%V)
                             (at level 20, q at level 50, format "l  d↦{# q }  v") : bi_scope.
  Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
  Local Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

  (** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Theorem read_fresh : forall σ g a b,
      let l := fresh_locs (dom (heap σ)) in
      σ.(world) !! uint.Z a = Some b ->
      relation.denote (ffi_step ReadOp (LitV $ LitInt a)) (σ,g) (state_insert_list l (Block_to_vals b) σ,g) (LitV $ LitLoc $ l).
  Proof.
    intros.
    simpl.
    monad_simpl.
    simpl.
    monad_simpl.
    econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
    apply relation.bind_runF.
    econstructor; eauto.
  Qed.

  Hint Resolve read_fresh : core.
  Hint Extern 1 (base_step (ExternalOp _ _) _ _ _ _ _) => econstructor; simpl : core.

  Lemma alloc_block_loc_not_null:
    ∀ (b: Block) σ1 l,
      isFresh σ1 l
      → ∀ l0 (x : val),
        heap_array l (Block_to_vals b) !! l0 = Some x
        → l0 ≠ null.
  Proof.
    intros v σ1 l H l0 x Heq.
    apply heap_array_lookup in Heq.
    destruct Heq as [l' (?&->&Heq)].
    apply H; eauto.
  Qed.

  Definition pointsto_block (l: loc) (q: dfrac) (b: Block) :=
    ([∗ map] l ↦ v ∈ heap_array l (Block_to_vals b), heap_pointsto l q v)%I.

  Lemma wp_ReadOp s E (a: u64) q b :
    {{{ ▷ uint.Z a d↦{q} b }}}
      ExternalOp ReadOp (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); uint.Z a d↦{q} b ∗
                                  pointsto_block l (DfracOwn 1) b }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _, _; simpl.
      constructor 1.
      rewrite /base_step /=.
      monad_simpl.
      simpl.
      monad_simpl.
      econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
      monad_simpl. }
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply base_step_atomic_inv in Hstep; [ | by inversion 1 ].
    inv_base_step.
    monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iMod (na_heap_alloc_list tls _ l (Block_to_vals b) (Reading O) with "Hσ")
      as "(Hσ & Hblock & Hl)".
    { rewrite length_Block_to_vals. rewrite /block_bytes. lia. }
    { destruct H1 as (?&?); eauto. }
    { destruct H1 as (H'&?); eauto. eapply H'. }
    { destruct H1 as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
        by rewrite (loc_add_0) in Hfresh.
    }
    { eauto. }
    iModIntro; iSplit; first done.
    iFrame.
    iApply "HΦ".
    iFrame.
    { rewrite /pointsto_block.
      iApply seq_pointsto_to_heap_array.
      iApply (big_sepL_mono with "Hl").
      iIntros (k x Heq) "(Hli&Hmt)".
      iApply (na_pointsto_to_heap with "Hli").
      destruct H1 as (H'&?). eapply H'.
    }
  Qed.

  Definition bindex_of_Z (i: Z) (Hlow: (0 <= i)%Z) (Hhi: (i < 4096)%Z) : fin block_bytes.
    cut (Z.to_nat i < 4096)%nat.
    { apply nat_to_fin. }
    change 4096%nat with (Z.to_nat 4096%Z).
    abstract (apply Z2Nat.inj_lt; auto; vm_compute; inversion 1).
  Defined.

  Theorem block_byte_index {ext: ffi_syntax} (b: Block) (i: Z) (Hlow: (0 <= i)%Z) (Hhi: (i < 4096)%Z) :
    Block_to_vals b !! Z.to_nat i = Some (LitV $ LitByte $ b !!! bindex_of_Z i Hlow Hhi).
  Proof.
    unfold Block_to_vals.
    rewrite ?list_lookup_fmap.
    unfold bindex_of_Z.
    destruct (vlookup_lookup' b (Z.to_nat i) (b !!! bindex_of_Z i Hlow Hhi)) as [H _].
    rewrite H; eauto.
  Qed.

  Theorem pointsto_block_extract i l q b :
    (0 <= i)%Z ->
    (i < 4096)%Z ->
    ⊢ pointsto_block l q b -∗ ∃ v, heap_pointsto (l +ₗ i) q v ∗ ⌜Block_to_vals b !! Z.to_nat i = Some v⌝.
  Proof.
    unfold pointsto_block; intros Hlow Hhi.
    iIntros "Hm".
    pose proof (block_byte_index b i ltac:(auto) ltac:(auto)) as Hi.
    assert (heap_array l (Block_to_vals b) !! (l +ₗ i) =
            Some $ LitV $ LitByte $ b !!! bindex_of_Z i Hlow Hhi) as Hha.
    { apply heap_array_lookup.
      eexists; intuition eauto. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hha with "Hm") as "(Hmi&_)".
    iExists _.
    iFrame "Hmi".
    destruct_with_eqn (Block_to_vals b !! Z.to_nat i); auto.
  Qed.

  Theorem heap_valid_block l b q σ :
    na_heap.na_heap_ctx tls σ -∗ pointsto_block l q b -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < 4096)%Z ->
                match σ !! (l +ₗ i) with
             | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
             | _ => False
                end) ⌝.
  Proof.
    iIntros "Hσ Hm".
    iIntros (i Hbound1 Hbound2).
    iDestruct (pointsto_block_extract i with "Hm") as (v) "[Hi %]"; eauto.
    iDestruct (heap_pointsto_na_acc with "Hi") as "[Hi Hi_rest]".
    iDestruct (@na_heap.na_heap_read with "Hσ Hi") as %(lk&?&Hlookup&Hlock).
    destruct lk; inversion Hlock; subst. rewrite Hlookup //.
  Qed.

  Theorem Block_to_vals_ext_eq b1 b2 :
    (forall (i:Z), (0 <= i)%Z -> (i < 4096)%Z ->
              Block_to_vals b1 !! Z.to_nat i = Block_to_vals b2 !! Z.to_nat i) ->
    b1 = b2.
  Proof.
    intros.
    assert (Block_to_vals b1 = Block_to_vals b2).
    { apply (list_eq_same_length _ _ 4096%nat);
        rewrite ?length_Block_to_vals; auto; intros.
      rewrite <- (Nat2Z.id i) in H1, H2.
      rewrite H in H1; try lia; congruence. }
    apply vec_to_list_inj2.
    apply list_fmap_eq_inj in H0; auto.
    hnf; intros.
    inversion H1; subst; auto.
  Qed.

  Lemma wp_WriteOp s E (a: u64) b q l :
    {{{ ▷ ∃ b0, uint.Z a d↦{#1} b0 ∗ pointsto_block l q b }}}
      ExternalOp WriteOp (Val $ PairV (LitV $ LitInt a) (LitV $ LitLoc l)) @ s; E
    {{{ RET LitV LitUnit; uint.Z a d↦{#1} b ∗ pointsto_block l q b}}}.
  Proof.
    iIntros (Φ) ">H Hϕ". iDestruct "H" as (b0) "(Ha&Hl)".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iDestruct (heap_valid_block with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      econstructor; eauto; [ econstructor; eauto| monad_simpl ]. }
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply base_step_atomic_inv in Hstep; [ | by inversion 1 ].
    inv_base_step.
    monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iMod (@gen_heap_update with "Hd Ha") as "[$ Ha]".
    assert (b = b1); [ | subst b1 ].
    { apply Block_to_vals_ext_eq; intros.
      specialize (H0 i); specialize (H2 i); intuition.
      simpl in H4.
      destruct_with_eqn (σ1.(heap) !! (l +ₗ i)); try contradiction.
      destruct p as (n0&?); destruct n0; try contradiction; congruence. }
    iModIntro; iSplit; first done.
    iFrame.
    iApply ("Hϕ" with "[$]").
  Qed.

  Definition disk_array (l: Z) (q: dfrac) (vs: list Block): iProp Σ :=
    ([∗ list] i ↦ b ∈ vs, (l + i) d↦{q} b)%I.

  Theorem disk_array_cons l q b vs :
    disk_array l q (b::vs) ⊣⊢
               pointsto l q b ∗ disk_array (l + 1) q vs.
  Proof.
    rewrite /disk_array big_sepL_cons.
    rewrite Z.add_0_r.
    assert (forall l k, l + S k = l + 1 + k) by lia.
    setoid_rewrite H.
    reflexivity.
  Qed.

  Theorem disk_array_app l q vs1 vs2 :
    disk_array l q (vs1 ++ vs2) ⊣⊢
               disk_array l q vs1 ∗ disk_array (l + length vs1) q vs2.
  Proof.
    rewrite /disk_array big_sepL_app.
    setoid_rewrite Nat2Z.inj_add.
    by setoid_rewrite Z.add_assoc.
  Qed.

  Theorem disk_array_emp l q :
    disk_array l q [] ⊣⊢ emp.
  Proof. by rewrite /disk_array. Qed.

  Theorem disk_array_split l q z vs :
    0 <= z < Z.of_nat (length vs) ->
    disk_array l q vs ⊣⊢
               disk_array l q (take (Z.to_nat z) vs) ∗
               disk_array (l + z) q (drop (Z.to_nat z) vs).
  Proof.
    intros.
    rewrite -[vs in (disk_array _ _ vs)](take_drop (Z.to_nat z)).
    rewrite disk_array_app length_take.
    rewrite Nat2Z.inj_min.
    rewrite Z.min_l; last lia.
    rewrite Z2Nat.id; last lia.
    auto.
  Qed.

  Lemma disk_array_acc_disc (l: Z) bs (z: Z) b q :
    0 <= z ->
    bs !! Z.to_nat z = Some b →
    disk_array l q bs -∗ ((l + z) d↦{q} b ∗
                          <bdisc> ∀ b', (l + z) d↦{q} b' -∗
                                                disk_array l q (<[Z.to_nat z:=b']>bs))%I.
  Proof.
    iIntros (Hpos Hlookup) "Hl".
    rewrite -[X in (disk_array l q X)](take_drop_middle _ (Z.to_nat z) b); last done.
    iDestruct (disk_array_app with "Hl") as "[Hl1 Hl]".
    iDestruct (disk_array_cons with "Hl") as "[Hl2 Hl3]".
    assert (Z.to_nat z < length bs)%nat as H by (apply lookup_lt_is_Some; by eexists).
    rewrite length_take min_l; last by lia.
    rewrite Z2Nat.id; auto. iFrame "Hl2".
    iModIntro. iIntros (w) "Hl2".
    clear Hlookup. assert (<[Z.to_nat z:=w]> bs !! Z.to_nat z = Some w) as Hlookup.
    { apply list_lookup_insert_eq. lia. }
    rewrite -[in (disk_array l q (<[Z.to_nat z:=w]> bs))](take_drop_middle (<[Z.to_nat z:=w]> bs) (Z.to_nat z) w Hlookup).
    iApply disk_array_app. rewrite take_insert_ge; last by lia. iFrame.
    iApply disk_array_cons. rewrite length_take min_l; last by lia. iFrame.
    rewrite drop_insert_lt; last by lia.
    rewrite Z2Nat.id; auto. iFrame.
  Qed.

  Lemma disk_array_acc (l: Z) bs (z: Z) b q :
    0 <= z ->
    bs !! Z.to_nat z = Some b →
    disk_array l q bs -∗ ((l + z) d↦{q} b ∗
                          ∀ b', (l + z) d↦{q} b' -∗
                                disk_array l q (<[Z.to_nat z:=b']>bs))%I.
  Proof.
    iIntros (Hpos Hlookup) "Hl".
    iDestruct (disk_array_acc_disc with "[$]") as "($&?)"; eauto.  rewrite own_discrete_elim; eauto.
  Qed.

  Lemma disk_array_acc_read (l: Z) bs (z: Z) b q :
    0 <= z ->
    bs !! Z.to_nat z = Some b →
    disk_array l q bs -∗ ((l + z) d↦{q} b ∗
                          ((l + z) d↦{q} b -∗
                                disk_array l q bs))%I.
  Proof.
    iIntros (??) "Hl".
    iDestruct (disk_array_acc with "Hl") as "[$ Hrest]"; eauto.
    iIntros "Hlz".
    iDestruct ("Hrest" with "Hlz") as "Hl".
    rewrite list_insert_id //.
  Qed.

  Lemma init_disk_sz_lookup_ge sz z:
    Z.of_nat sz <= z →
    (init_disk ∅ sz : gmap Z Block) !! z = None.
  Proof.
    induction sz => Hle.
    - apply lookup_empty.
    - rewrite lookup_insert_ne; first apply IHsz; lia.
  Qed.

  Lemma disk_array_init_disk sz:
    ([∗ map] i↦b ∈ init_disk ∅ sz, i d↦{#1} b) ⊢@{_} disk_array 0 (DfracOwn 1) (replicate sz (block0 : Block)).
  Proof.
    induction sz; rewrite /init_disk-/init_disk/disk_array.
    - rewrite big_sepM_empty big_sepL_nil //=.
    - rewrite replicate_S_end.
      rewrite big_sepL_app.
      rewrite length_replicate big_sepL_cons big_sepL_nil.
      rewrite big_sepM_insert.
      * rewrite comm. apply bi.sep_mono; auto. by rewrite ?right_id Z.add_0_l.
      * by apply init_disk_sz_lookup_ge.
  Qed.

End disk.

Notation "l d↦{ q } v" := (pointsto (L:=Z) (V:=Block) l q%Qp v%V)
                            (at level 20, q at level 50, format "l  d↦{ q }  v") : bi_scope.
Notation "l d↦ v" := (pointsto (L:=Z) (V:=Block) l (DfracOwn 1) v%V)
                       (at level 20, format "l  d↦  v") : bi_scope.
Notation "l d↦∗ vs" := (disk_array l (DfracOwn 1) vs%V)
                       (at level 20, format "l  d↦∗  vs") : bi_scope.
