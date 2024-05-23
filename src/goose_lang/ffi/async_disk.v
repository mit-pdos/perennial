From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import ghost_async_map log_heap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import ectx_lifting.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang.ffi Require Export async_disk_syntax.

Set Default Proof Using "Type".
Set Printing Projections.

Definition disk_state := gmap Z (async Block).

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state () _ _).
Defined.

Fixpoint init_disk (d: disk_state) (sz: nat) : disk_state :=
  match sz with
  | O => d
  | S n => <[(Z.of_nat n) := sync block0]> (init_disk d n)
  end.

Lemma length_Block_to_vals {ext: ffi_syntax} b :
    length (Block_to_vals b) = block_bytes.
Proof.
  rewrite /Block_to_vals fmap_length vec_to_list_length //.
Qed.

Lemma replicate_zero_to_block0 `{ext_ty: ext_types} :
  replicate (uint.nat 4096) (zero_val byteT) =
  Block_to_vals block0.
Proof. reflexivity. Qed.

Class diskGS Σ : Set := DiskGS
  { diskG_ghost_async_mapG :> ghost_async_mapG Σ Z Block ;
    diskG_ghost_async_name : gname }.

Class disk_preG Σ :=
  { disk_preG_ghost_async_mapG :> ghost_async_mapG Σ Z Block }.

Definition diskΣ : gFunctors :=
  #[ghost_async_mapΣ Z Block].

#[global]
Instance subG_diskG Σ : subG diskΣ Σ → disk_preG Σ.
Proof. solve_inG. Qed.

Definition disk_update_pre {Σ} (dG: disk_preG Σ) (n: gname) :=
  {| diskG_ghost_async_mapG := disk_preG_ghost_async_mapG;
     diskG_ghost_async_name := n |}.

Section disk.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model disk_ty.

  Definition disk_val (d : ()) : val := ExtV d.

  Definition Get: val :=
    λ: <>, disk_val ().

  Definition Read: val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    raw_slice byteT (Var "p") #4096.

  Definition ReadTo: val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp (Var "a") in
    MemCpy_rec byteT (slice.ptr (Var "buf")) (Var "p") #4096.

  (*
  Theorem Read_t : ⊢ Read : (uint64T -> blockT).
  Proof.
    typecheck.
  Qed.
  *)

  Definition Write: val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  (*
  Theorem Write_t : ⊢ Write : (uint64T -> slice.T byteT -> unitT).
  Proof.
    typecheck.
  Qed.
  *)

  Definition Barrier: val :=
    λ: <>, ExternalOp BarrierOp #().

  Definition Size: val :=
    λ: "v",
       ExternalOp SizeOp (Var "v").

  Theorem Size_t : ∅ ⊢ Size #() : uint64T.
  Proof.
    rewrite /Size.
     eapply external_hasTy; eauto.
    - eapply (DiskOpType (SizeOp)).
    - typecheck.
  Qed.

  (*
  Theorem Size_t : ∅ ⊢ Size : (unitT -> uint64T).
  Proof.
    typecheck.
    econstructor.
  Qed.
   *)

  Existing Instances r_mbind r_fmap.

  Definition highest_addr (addrs: gset Z): Z :=
    set_fold (λ k r, k `max` r)%Z 0%Z addrs.

  Definition disk_size {A} (d: gmap Z A): Z :=
    1 + highest_addr (dom d).

  Definition flush_disk (d : @ffi_state disk_model) : @ffi_state disk_model := flush <$> d.

  Definition ffi_step (op: DiskOp) (v: val): transition (state*global_state) expr :=
    match op, v with
    | ReadOp, LitV (LitInt a) =>
      ab ← reads (λ '(σ,g), σ.(world) !! uint.Z a) ≫= unwrap;
      l ← allocateN;
      modify (λ '(σ,g), (state_insert_list l (Block_to_vals (latest ab)) σ, g));;
      ret $ Val $ #(LitLoc l)
    | WriteOp, PairV (LitV (LitInt a)) (LitV (LitLoc l)) =>
      old ← reads (λ '(σ,g), σ.(world) !! uint.Z a) ≫= unwrap;
      b ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) b, (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
                | _ => False
                end));
      modify (λ '(σ,g), (set world <[ uint.Z a := async_put b old ]> σ, g));;
      ret $ Val $ #()
    | SizeOp, LitV LitUnit =>
      sz ← reads (λ '(σ,g), disk_size σ.(world));
      ret $ Val $ LitV $ LitInt (word.of_Z sz)
    | BarrierOp, LitV LitUnit =>
      modify (λ '(σ,g), (set world flush_disk σ, g));;
      ret $ Val $ #()
    | _, _ => undefined
    end.

  (* Holds if b is something that addr's contents could change to after crash *)
  Definition is_possible (d : @ffi_state disk_model) (addr: Z) (b: Block) : Prop :=
    ∃ ab, d !! addr = Some ab ∧ b ∈ possible ab.

  Inductive ffi_crash_step : @ffi_state disk_model → @ffi_state disk_model → Prop :=
  | async_crash d d' :
      dom d = dom d' ∧
      (∀ (addr : Z) (ab : async Block), d' !! addr = Some ab →
       ∃ (b : Block), ab = sync b ∧ is_possible d addr b) →
      ffi_crash_step d d'.

  (* these instances are also local (to the outer section) *)
  Instance disk_semantics : ffi_semantics disk_op disk_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := ffi_crash_step; }.

  Program Instance disk_interp: ffi_interp disk_model :=
    {| ffiLocalGS := diskGS;
       ffiGlobalGS _ := ()%type;
       ffi_local_ctx Σ _ (d: @ffi_state disk_model) := ghost_async_map_auth (diskG_ghost_async_name) 1 d;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ _ (d: @ffi_state disk_model) :=
       ([∗ map] l↦v ∈ d, (ghost_async_map_elem (K:=Z) (V:=Block) (diskG_ghost_async_name)
                                               l (DfracOwn 1) (list_to_set (pending v)) (latest v)))%I;
       ffi_global_start _ _ _ := True%I;
       ffi_restart := fun _ _ (d: @ffi_state disk_model) => True%I;
       (* TODO: need to actually say that the gname changes and σ2 should be a crashed version of σ1 *)
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 :=
         (⌜ (@diskG_ghost_async_mapG _ hF1 = @diskG_ghost_async_mapG _ hF2) ⌝ ∗
         ghost_async_map_exchanger (@diskG_ghost_async_name _ hF1) σ1 (@diskG_ghost_async_name _ hF2) σ2)%I
    |}.

  Section proof.
  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
  Instance goose_diskGS : diskGS Σ := goose_ffiLocalGS.

  Notation "l d↦{ dq }[ a ] v" := (ghost_async_map_elem (K:=Z) (V:=Block) (diskG_ghost_async_name)
                                                        l dq a v%V)
                             (at level 20, dq at level 50, format "l  d↦{ dq }[ a ]  v") : bi_scope.
  Notation "l d↦{# q }[ a ] v" := (ghost_async_map_elem (K:=Z) (V:=Block) (diskG_ghost_async_name)
                                                        l (DfracOwn q) a v%V)
                             (at level 20, q at level 50, format "l  d↦{# q }[ a ]  v") : bi_scope.
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

  (*
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
   *)

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
    ([∗ map] l ↦ v ∈ heap_array l (Block_to_vals b), l ↦{q} v)%I.

  Lemma wp_ReadOp s E (a: u64) aset q b :
    {{{ ▷ uint.Z a d↦{q}[aset] b }}}
      ExternalOp ReadOp (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); uint.Z a d↦{q}[aset] b ∗
                                  pointsto_block l (DfracOwn 1) b }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ". iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iDestruct (@ghost_async_map_lookup with "Hd Ha") as %Hlookup.
    destruct Hlookup as (vm&Hw&Hlatest&Hpend).
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
    iMod (na_heap_alloc_list tls _ l (Block_to_vals (latest vm)) (Reading O) with "Hσ")
      as "(Hσ & Hblock & Hl)".
    { rewrite length_Block_to_vals. rewrite /block_bytes. lia. }
    { destruct H0 as (?&?); eauto. }
    { destruct H0 as (H'&?); eauto. eapply H'. }
    { destruct H0 as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
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
      destruct H0 as (H'&?). eapply H'.
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
    ⊢ pointsto_block l q b -∗ ∃ v, (l +ₗ i) ↦{q} v ∗ ⌜Block_to_vals b !! Z.to_nat i = Some v⌝.
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

  (* TODO: it is possible to derive a version where full 1 ownership is not required *)
  Lemma wp_BarrierOp s E m :
    {{{ ▷ [∗ map] a ↦ b ∈ m, ∃ aset, a d↦{#1}[aset] b }}}
      ExternalOp BarrierOp (LitV LitUnit) @ s; E
    {{{ RET LitV LitUnit; [∗ map] a ↦ b ∈ m, a d↦{#1}[∅] b }}}.
  Proof.
    iIntros (Φ) ">H Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iSplit.
    { iPureIntro.
      eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn). }
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply base_step_atomic_inv in Hstep; [ | by inversion 1 ].
    inv_base_step.
    monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iMod (ghost_async_map_update_flush_big with "Hd H") as "[$ Ha]".
    iModIntro; iSplit; first done.
    iFrame.
    iApply ("Hϕ" with "[$]").
  Qed.

  Lemma wp_WriteOp s E (a: u64) aset b0 b q l :
    {{{ ▷ (uint.Z a d↦{#1}[aset] b0 ∗ pointsto_block l q b) }}}
      ExternalOp WriteOp (Val $ PairV (LitV $ LitInt a) (LitV $ LitLoc l)) @ s; E
    {{{ RET LitV LitUnit; uint.Z a d↦{#1}[{[b0]} ∪ aset] b ∗ pointsto_block l q b}}}.
  Proof.
    iIntros (Φ) ">H Hϕ". iDestruct "H" as "(Ha&Hl)".
    iApply wp_lift_atomic_base_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iDestruct (@ghost_async_map_lookup with "Hd Ha") as %Hlookup.
    destruct Hlookup as (vm&Hw&Hlatest&Hpend).
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
    iMod (ghost_async_map_async_put with "Hd Ha") as "[$ Ha]".
    { eauto. }
    assert (b = b0); [ | subst b0 ].
    { apply Block_to_vals_ext_eq; intros.
      specialize (H i); specialize (H1 i); intuition.
      simpl in H3.
      destruct_with_eqn (σ1.(heap) !! (l +ₗ i)); try contradiction.
      destruct p as (n0&?); destruct n0; try contradiction; congruence. }
    iModIntro; iSplit; first done.
    iFrame.
    iApply ("Hϕ" with "[$]").
  Qed.

  Definition disk_array (l: Z) (q: dfrac) (vs: list Block): iProp Σ :=
    ([∗ list] i ↦ b ∈ vs, (l + i) d↦{q}[∅] b)%I.

  Theorem disk_array_cons l q b vs :
    disk_array l q (b::vs) ⊣⊢
               l d↦{q}[∅] b ∗ disk_array (l + 1) q vs.
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
    rewrite disk_array_app take_length.
    rewrite Nat2Z.inj_min.
    rewrite Z.min_l; last lia.
    rewrite Z2Nat.id; last lia.
    auto.
  Qed.

  Lemma disk_array_acc (l: Z) bs (z: Z) b q :
    0 <= z ->
    bs !! Z.to_nat z = Some b →
    disk_array l q bs -∗ ((l + z) d↦{q}[∅] b ∗
                          ∀ b', (l + z) d↦{q}[∅] b' -∗ disk_array l q (<[Z.to_nat z:=b']>bs))%I.
  Proof.
    iIntros (Hpos Hlookup) "Hl".
    rewrite -[X in (disk_array l q X)](take_drop_middle _ (Z.to_nat z) b); last done.
    iDestruct (disk_array_app with "Hl") as "[Hl1 Hl]".
    iDestruct (disk_array_cons with "Hl") as "[Hl2 Hl3]".
    assert (Z.to_nat z < length bs)%nat as H by (apply lookup_lt_is_Some; by eexists).
    rewrite take_length min_l; last by lia.
    rewrite Z2Nat.id; auto. iFrame "Hl2".
    iIntros (w) "Hl2".
    clear Hlookup. assert (<[Z.to_nat z:=w]> bs !! Z.to_nat z = Some w) as Hlookup.
    { apply list_lookup_insert. lia. }
    rewrite -[in (disk_array l q (<[Z.to_nat z:=w]> bs))](take_drop_middle (<[Z.to_nat z:=w]> bs) (Z.to_nat z) w Hlookup).
    iApply disk_array_app. rewrite take_insert; last by lia. iFrame.
    iApply disk_array_cons. rewrite take_length min_l; last by lia. iFrame.
    rewrite drop_insert_gt; last by lia.
    rewrite Z2Nat.id; auto. iFrame.
  Qed.

  Lemma init_disk_sz_lookup_ge sz z:
    Z.of_nat sz <= z →
    (init_disk ∅ sz : gmap Z _) !! z = None.
  Proof.
    induction sz => Hle.
    - apply lookup_empty.
    - rewrite lookup_insert_ne; first apply IHsz; lia.
  Qed.

  Lemma disk_array_init_disk sz:
    ([∗ map] i↦b ∈ init_disk ∅ sz, i d↦{#1}[list_to_set (pending b)] (latest b)) -∗
    disk_array 0 (DfracOwn 1) (replicate sz (block0 : Block)).
  Proof.
    induction sz; rewrite /init_disk-/init_disk/disk_array.
    - rewrite big_sepM_empty big_sepL_nil //=. auto.
    - rewrite replicate_S_end.
      rewrite big_sepL_app.
      rewrite replicate_length big_sepL_cons big_sepL_nil.
      rewrite big_sepM_insert.
      * iIntros "(H1&H2)".
        iSplitL "H2".
        { iApply IHsz.  eauto. }
        { rewrite ?right_id Z.add_0_l. simpl latest. simpl list_to_set. eauto. }
      * by apply init_disk_sz_lookup_ge.
  Qed.

  End proof.

End disk.

Global Opaque Write Read Size Barrier.

Notation "l d↦{ q }[ a ] v" := (ghost_async_map_elem (K:=Z) (V:=Block) (diskG_ghost_async_name) l q%Qp a v%V)
                            (at level 20, q at level 50, format "l  d↦{ q }[ a ]  v") : bi_scope.
Notation "l d↦[ a ] v" := (ghost_async_map_elem (K:=Z) (V:=Block) (diskG_ghost_async_name) l (DfracOwn 1) a v%V)
                       (at level 20, format "l  d↦[ a ]  v") : bi_scope.
Notation "l d↦∗ vs" := (disk_array l (DfracOwn 1) vs%V)
                       (at level 20, format "l  d↦∗  vs") : bi_scope.

From Perennial.goose_lang Require Import adequacy.

#[global]
Program Instance disk_interp_adequacy:
  @ffi_interp_adequacy disk_model disk_interp disk_op disk_semantics :=
  {| ffiGpreS := disk_preG;
     ffiΣ := diskΣ;
     subG_ffiPreG := subG_diskG;
     ffi_initgP := λ _, True;
     ffi_initP := λ _ _, True;
  |}.
Next Obligation. rewrite //=. iIntros (Σ hPre g). eauto. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ?) "_".
  iMod (ghost_async_map_alloc σ) as (?) "H".
  iExists (DiskGS _ _ _). by iFrame.
Qed.
Next Obligation.
  iIntros (Σ σ σ' Hcrash Hold) "Hinterp".
  iMod (ghost_async_map_exchanger_init _ σ σ' with "[$]") as (γ') "(Hauth&Hexch)".
  { inversion Hcrash; eauto. }
  iExists {| diskG_ghost_async_mapG := diskG_ghost_async_mapG; diskG_ghost_async_name := γ' |}.
  by iFrame.
Qed.

Section crash.
  Existing Instances async_disk_syntax.disk_op async_disk.disk_model async_disk_syntax.disk_ty.
  Existing Instances async_disk.disk_semantics async_disk.disk_interp.
  Existing Instance goose_diskGS.

  Lemma disk_pointsto_post_crash `{!heapGS Σ} l a v:
    l d↦[a] v ⊢@{_} post_crash (λ _, ∃ v', ⌜ v' ∈ {[v]} ∪ a ⌝ ∗ l d↦[∅] v').
  Proof.
    iIntros "H". iIntros (???) "Hrel".
    rewrite /ffi_crash_rel. simpl.
    iDestruct "Hrel" as "(%Heq&Hrel)".
    iDestruct (@ghost_async_map_swap with "[$] [H]") as "(H&Hrel)"; last by iFrame.
    { rewrite Heq. by iFrame. }
  Qed.

  Lemma disk_pointsto_post_crash' `{!heapGS Σ} l v:
    l d↦[∅] v ⊢@{_} post_crash (λ _, l d↦[∅] v).
  Proof.
    iIntros "H". iIntros (???) "Hrel".
    rewrite /ffi_crash_rel. simpl.
    iDestruct "Hrel" as "(%Heq&Hrel)".
    iDestruct (@ghost_async_map_swap with "[$] [H]") as "(H&Hrel)".
    { rewrite Heq. by iFrame. }
    iDestruct "Hrel" as (v') "(%Hin&Hl)".
    set_unfold in Hin. destruct Hin as [->|[]].
    iFrame. eauto.
  Qed.

  Global Instance disk_pointsto_into_crash `{!heapGS Σ} l a v:
    IntoCrash (l d↦[a] v)%I (λ hG, ∃v', ⌜ v' ∈ {[v]} ∪ a ⌝ ∗ l d↦[∅] v')%I.
  Proof. apply disk_pointsto_post_crash. Qed.

  Global Instance disk_array_into_crash `{!heapGS Σ} l vs:
    IntoCrash (l d↦∗ vs)%I (λ _, l d↦∗ vs)%I.
  Proof. apply big_sepL_into_crash. intros. apply disk_pointsto_post_crash'. Qed.
End crash.
