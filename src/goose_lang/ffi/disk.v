From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import ectx_lifting.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing.
From Perennial.goose_lang Require Import crash_modality.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

Inductive DiskOp := ReadOp | WriteOp | SizeOp.
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  solve_decision.
Defined.

Instance DiskOp_fin : Countable DiskOp.
Proof.
  solve_countable DiskOp_rec 3%nat.
Qed.

Definition disk_op : ffi_syntax.
Proof.
  refine (mkExtOp DiskOp _ _ () _ _).
Defined.

Inductive Disk_ty := | DiskInterfaceTy.

Instance disk_val_ty: val_types :=
  {| ext_tys := Disk_ty; |}.

Section disk.
  Existing Instances disk_op disk_val_ty.

  Inductive disk_ext_tys : @val disk_op -> (ty * ty) -> Prop :=
  | DiskOpType op :
      disk_ext_tys (λ: "v", ExternalOp op (Var "v"))%V
                   (match op with
                   | ReadOp => (uint64T, arrayT byteT)
                   | WriteOp => (prodT uint64T (arrayT byteT), unitT)
                   | SizeOp => (unitT, uint64T)
                   end).

  Definition disk_ty: ext_types disk_op :=
    {| val_tys := disk_val_ty;
       get_ext_tys := disk_ext_tys |}.
  Definition Disk: ty := extT DiskInterfaceTy.
End disk.

Definition block_bytes: nat := Z.to_nat 4096.
Definition BlockSize {ext: ffi_syntax}: val := #4096.
Definition Block := vec byte block_bytes.
Definition blockT `{ext_tys:ext_types}: @ty val_tys := slice.T byteT.
(* TODO: could use vreplicate; not sure how much easier it is to work with *)
Definition block0 : Block := list_to_vec (replicate (Z.to_nat 4096) (U8 0)).


Lemma block_bytes_eq : block_bytes = Z.to_nat 4096.
Proof. reflexivity. Qed.

Global Instance Block0: Inhabited Block := _.
Global Instance Block_countable : Countable Block := _.

Definition disk_state := gmap Z Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state () _ _).
Defined.

Fixpoint init_disk (d: disk_state) (sz: nat) : disk_state :=
  match sz with
  | O => d
  | S n => <[(Z.of_nat n) := block0]> (init_disk d n)
  end.

Definition Block_to_vals {ext: ffi_syntax} (bl:Block) : list val :=
  fmap b2val (vec_to_list bl).

Lemma length_Block_to_vals {ext: ffi_syntax} b :
    length (Block_to_vals b) = block_bytes.
Proof.
  rewrite /Block_to_vals fmap_length vec_to_list_length //.
Qed.

Lemma replicate_zero_to_block0 `{ext_ty: ext_types} :
  replicate (int.nat 4096) (zero_val byteT) =
  Block_to_vals block0.
Proof. reflexivity. Qed.

Class diskG Σ :=
  { diskG_gen_heapG :> gen_heap.gen_heapGS Z Block Σ; }.


Class disk_preG Σ :=
  { disk_preG_gen_heapG :> gen_heap.gen_heapGpreS Z Block Σ; }.

Definition diskΣ : gFunctors :=
  #[gen_heapΣ Z Block].

Instance subG_diskG Σ : subG diskΣ Σ → disk_preG Σ.
Proof. solve_inG. Qed.

Definition disk_update_pre {Σ} (dG: disk_preG Σ) (n: gen_heap_names) :=
  {| diskG_gen_heapG := gen_heapG_update_pre (@disk_preG_gen_heapG _ dG) n |}.

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
    λ: <>, #().

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

  Definition disk_size (d: gmap Z Block): Z :=
    1 + highest_addr (dom _ d).

  Definition ffi_step (op: DiskOp) (v: val): transition (state*global_state) val :=
    match op, v with
    | ReadOp, LitV (LitInt a) =>
      b ← reads (λ '(σ,g), σ.(world) !! int.Z a) ≫= unwrap;
      l ← allocateN;
      modify (λ '(σ,g), (state_insert_list l (Block_to_vals b) σ, g));;
      ret $ #(LitLoc l)
    | WriteOp, PairV (LitV (LitInt a)) (LitV (LitLoc l)) =>
      _ ← reads (λ '(σ,g), σ.(world) !! int.Z a) ≫= unwrap;
        (* TODO: use Sydney's executable version from disk_interpreter.v as
        the generator here *)
      b ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) b, (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
                | _ => False
                end));
      modify (λ '(σ,g), (set world <[ int.Z a := b ]> σ, g));;
      ret #()
    | SizeOp, LitV LitUnit =>
      sz ← reads (λ '(σ,g), disk_size σ.(world));
      ret $ LitV $ LitInt (word.of_Z sz)
    | _, _ => undefined
    end.

  (* these instances are also local (to the outer section) *)
  Instance disk_semantics : ffi_semantics disk_op disk_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }.

  Program Instance disk_interp: ffi_interp disk_model :=
    {| ffiG := diskG;
       ffi_local_names := gen_heap_names;
       ffi_global_names := unit;
       ffi_get_local_names := fun _ hD => gen_heapG_get_names (diskG_gen_heapG);
       ffi_get_global_names := fun _ hD => tt;
       ffi_update_local := fun _ hD names =>
                       {| diskG_gen_heapG := gen_heapG_update (@diskG_gen_heapG _ hD) names |};
       ffi_get_update := fun _ _ => _;
       ffi_ctx := fun _ _ (d: @ffi_state disk_model) => gen_heap.gen_heap_interp d;
       ffi_global_ctx := fun _ _ _ => True%I;
       ffi_local_start := fun _ _ (d: @ffi_state disk_model) _ =>
                      ([∗ map] l↦v ∈ d, (gen_heap.mapsto (L:=Z) (V:=Block) l (DfracOwn 1) v))%I;
       ffi_restart := fun _ _ (d: @ffi_state disk_model) => True%I;
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ hF1 = hF2 ∧ σ1 = σ2 ⌝%I;
    |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.

  Section proof.
  Context `{!heapGS Σ}.
  Instance diskG0 : diskG Σ := heapG_ffiG.

  Notation "l d↦{ dq } v" := (gen_heap.mapsto (L:=Z) (V:=Block) l dq v%V)
                             (at level 20, dq at level 50, format "l  d↦{ dq }  v") : bi_scope.
  Notation "l d↦{# q } v" := (gen_heap.mapsto (L:=Z) (V:=Block) l (DfracOwn q) v%V)
                             (at level 20, q at level 50, format "l  d↦{# q }  v") : bi_scope.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
  Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

  (** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Theorem read_fresh : forall σ g a b,
      let l := fresh_locs (dom (gset loc) (heap σ)) in
      σ.(world) !! int.Z a = Some b ->
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
  Hint Extern 1 (head_step (ExternalOp _ _) _ _ _ _ _) => econstructor; simpl : core.

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

  Definition mapsto_block (l: loc) (q: Qp) (b: Block) :=
    ([∗ map] l ↦ v ∈ heap_array l (Block_to_vals b), l ↦{q} v)%I.

  Lemma wp_ReadOp s E (a: u64) q b :
    {{{ ▷ int.Z a d↦{q} b }}}
      ExternalOp ReadOp (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); int.Z a d↦{q} b ∗
                                  mapsto_block l 1 b }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _, _; simpl.
      constructor 1.
      rewrite /head_step /=.
      monad_simpl.
      simpl.
      monad_simpl.
      econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
      monad_simpl. }
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply head_step_atomic_inv in Hstep; [ | by inversion 1 ].
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    inv_head_step.
    monad_inv.
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
    { rewrite /mapsto_block.
      iApply seq_mapsto_to_heap_array.
      iApply (big_sepL_mono with "Hl").
      iIntros (k x Heq) "(Hli&Hmt)".
      iApply (na_mapsto_to_heap with "Hli").
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

  Theorem mapsto_block_extract i l q b :
    (0 <= i)%Z ->
    (i < 4096)%Z ->
    ⊢ mapsto_block l q b -∗ ∃ v, (l +ₗ i) ↦{q} v ∗ ⌜Block_to_vals b !! Z.to_nat i = Some v⌝.
  Proof.
    unfold mapsto_block; intros Hlow Hhi.
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
    na_heap.na_heap_ctx tls σ -∗ mapsto_block l q b -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < 4096)%Z ->
                match σ !! (l +ₗ i) with
             | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
             | _ => False
                end) ⌝.
  Proof.
    iIntros "Hσ Hm".
    iIntros (i Hbound1 Hbound2).
    iDestruct (mapsto_block_extract i with "Hm") as (v) "[Hi %]"; eauto.
    iDestruct (heap_mapsto_na_acc with "Hi") as "[Hi Hi_rest]".
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
    apply fmap_inj in H0; auto.
    hnf; intros.
    inversion H1; subst; auto.
  Qed.

  Lemma wp_WriteOp s E (a: u64) b q l :
    {{{ ▷ ∃ b0, int.Z a d↦{#1} b0 ∗ mapsto_block l q b }}}
      ExternalOp WriteOp (Val $ PairV (LitV $ LitInt a) (LitV $ LitLoc l)) @ s; E
    {{{ RET LitV LitUnit; int.Z a d↦{#1} b ∗ mapsto_block l q b}}}.
  Proof.
    iIntros (Φ) ">H Hϕ". iDestruct "H" as (b0) "(Ha&Hl)".
    iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iDestruct (heap_valid_block with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      econstructor; eauto; [ econstructor; eauto| monad_simpl ]. }
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply head_step_atomic_inv in Hstep; [ | by inversion 1 ].
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    inv_head_step.
    monad_inv.
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
               mapsto l q b ∗ disk_array (l + 1) q vs.
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
    rewrite take_length min_l; last by lia.
    rewrite Z2Nat.id; auto. iFrame "Hl2".
    iModIntro. iIntros (w) "Hl2".
    clear Hlookup. assert (<[Z.to_nat z:=w]> bs !! Z.to_nat z = Some w) as Hlookup.
    { apply list_lookup_insert. lia. }
    rewrite -[in (disk_array l q (<[Z.to_nat z:=w]> bs))](take_drop_middle (<[Z.to_nat z:=w]> bs) (Z.to_nat z) w Hlookup).
    iApply disk_array_app. rewrite take_insert; last by lia. iFrame.
    iApply disk_array_cons. rewrite take_length min_l; last by lia. iFrame.
    rewrite drop_insert_gt; last by lia.
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

  Lemma init_disk_sz_lookup_ge sz z:
    Z.of_nat sz <= z →
    (init_disk ∅ sz : gmap Z Block) !! z = None.
  Proof.
    induction sz => Hle.
    - apply lookup_empty.
    - rewrite lookup_insert_ne; first apply IHsz; lia.
  Qed.

  Lemma disk_array_init_disk sz:
    ([∗ map] i↦b ∈ init_disk ∅ sz, i d↦{#1} b) -∗ disk_array 0 (DfracOwn 1) (replicate sz (block0 : Block)).
  Proof.
    induction sz; rewrite /init_disk-/init_disk/disk_array.
    - rewrite big_sepM_empty big_sepL_nil //=.
    - rewrite replicate_S_end.
      rewrite big_sepL_app.
      rewrite replicate_length big_sepL_cons big_sepL_nil.
      rewrite big_sepM_insert.
      * rewrite comm. apply bi.sep_mono; auto. by rewrite ?right_id Z.add_0_l.
      * by apply init_disk_sz_lookup_ge.
  Qed.

  End proof.

End disk.

Global Opaque Write Read Size.

Notation "l d↦{ q } v" := (mapsto (L:=Z) (V:=Block) l q%Qp v%V)
                            (at level 20, q at level 50, format "l  d↦{ q }  v") : bi_scope.
Notation "l d↦ v" := (mapsto (L:=Z) (V:=Block) l (DfracOwn 1) v%V)
                       (at level 20, format "l  d↦  v") : bi_scope.
Notation "l d↦∗ vs" := (disk_array l (DfracOwn 1) vs%V)
                       (at level 20, format "l  d↦∗  vs") : bi_scope.

From Perennial.goose_lang Require Import adequacy.

Program Instance disk_interp_adequacy:
  @ffi_interp_adequacy disk_model disk_interp disk_op disk_semantics :=
  {| ffi_preG := disk_preG;
     ffiΣ := diskΣ;
     subG_ffiPreG := subG_diskG;
     ffi_initgP := λ _, True;
     ffi_initP := λ _ _, True;
     ffi_update_pre := (λ _ hP names _, @disk_update_pre _ hP names);
     ffi_pre_global_start := (λ _ hP names _, True%I);
     ffi_pre_global_ctx := (λ _ hP names _, True%I);
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation. rewrite //=. intros ?? [] [] => //=. Qed.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. iIntros (Σ hPre g). eauto. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ???) "_". iMod (gen_heap_name_strong_init σ) as (names) "(Hctx&Hpts)".
  iExists names. by iFrame.
Qed.
Next Obligation.
  iIntros (Σ σ σ' g Hcrash Hold) "Hinterp Hg".
  iExists (ffi_get_local_names _ Hold) => //=.
  inversion Hcrash; subst.
  iFrame. iPureIntro; split_and!; auto.
  destruct Hold as [[]] => //=.
Qed.

Section crash.
  Existing Instances disk.disk_op disk.disk_model disk.disk_ty.
  Existing Instances disk.disk_semantics disk.disk_interp.
  Existing Instance diskG0.

  Lemma disk_mapsto_post_crash `{!heapGS Σ} l q v:
    l d↦{q} v -∗ post_crash (λ _, l d↦{q} v).
  Proof.
    iIntros "H". iIntros (???) "#Hrel".
    rewrite /ffi_crash_rel.
    iDestruct "Hrel" as %(Heq1&Heq2).
    rewrite /diskG0. rewrite Heq1. eauto.
  Qed.

  Global Instance disk_mapsto_into_crash `{!heapGS Σ} l q v:
    IntoCrash (l d↦{q} v)%I (λ hG, l d↦{q} v)%I.
  Proof. apply disk_mapsto_post_crash. Qed.

  Global Instance disk_array_into_crash `{!heapGS Σ} l vs:
    IntoCrash (l d↦∗ vs)%I (λ _, l d↦∗ vs)%I.
  Proof. apply _. Qed.
End crash.
