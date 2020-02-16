From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing.
From Perennial.algebra Require Import gen_heap.

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

Inductive Disk_val := | DiskInterfaceVal.
Instance eq_Disk_val : EqDecision Disk_val.
Proof.
  solve_decision.
Defined.

Instance eq_Disk_fin : Countable Disk_val.
Proof.
  solve_countable Disk_val_rec 1%nat.
Qed.

Definition disk_op : ext_op.
Proof.
  refine (mkExtOp DiskOp _ _ Disk_val _ _).
Defined.

Inductive Disk_ty := | DiskInterfaceTy.

Instance disk_val_ty: val_types :=
  {| ext_tys := Disk_ty; |}.

Section disk.
  Existing Instances disk_op disk_val_ty.
  Definition disk_ty: ext_types disk_op :=
    {| val_tys := disk_val_ty;
       val_ty_def x := match x with
                    | DiskInterfaceTy => DiskInterfaceVal
                       end;
       get_ext_tys (op: @external disk_op) :=
         match op with
      | ReadOp => (uint64T, arrayT byteT)
      | WriteOp => (prodT uint64T (arrayT byteT), unitT)
      | SizeOp => (unitT, uint64T)
         end; |}.
  Definition Disk: ty := extT DiskInterfaceTy.
End disk.

Definition block_bytes: nat := Z.to_nat 4096.
Definition BlockSize {ext: ext_op}: val := #4096.
Definition Block := vec byte block_bytes.
Definition blockT `{ext_tys:ext_types}: @ty val_tys := slice.T byteT.

Definition disk_state := gmap Z Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state _).
Defined.

Definition Block_to_vals {ext: ext_op} (bl:Block) : list val :=
  fmap b2val (vec_to_list bl).

Lemma length_Block_to_vals {ext: ext_op} b :
    length (Block_to_vals b) = block_bytes.
Proof.
  rewrite /Block_to_vals fmap_length vec_to_list_length //.
Qed.

Class diskG Σ :=
  { diskG_gen_heapG :> gen_heapG Z Block Σ; }.

Section disk.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model disk_ty.

  Definition Read: val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    raw_slice byteT (Var "p") #4096.

  Theorem Read_t : ⊢ Read : (uint64T -> blockT).
  Proof.
    typecheck.
  Qed.

  Definition Write: val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  Theorem Write_t : ⊢ Write : (uint64T -> slice.T byteT -> unitT).
  Proof.
    typecheck.
  Qed.

  Definition Barrier: val :=
    λ: <>, #().

  Definition Size: val :=
    λ: <>,
       ExternalOp SizeOp #().

  Theorem Size_t : ⊢ Size : (unitT -> uint64T).
  Proof.
    typecheck.
  Qed.

  Existing Instances r_mbind r_fmap.

  Definition highest_addr (addrs: gset Z): Z :=
    set_fold (λ k r, k `max` r)%Z 0%Z addrs.

  Definition disk_size (d: gmap Z Block): Z :=
    1 + highest_addr (dom _ d).

  Definition ext_step (op: DiskOp) (v: val): transition state val :=
    match op, v with
    | ReadOp, LitV (LitInt a) =>
      b ← reads (λ σ, σ.(world) !! int.val a) ≫= unwrap;
      l ← allocateN 4096;
      modify (state_insert_list l (Block_to_vals b));;
      ret $ #(LitLoc l)
    | WriteOp, PairV (LitV (LitInt a)) (LitV (LitLoc l)) =>
      _ ← reads (λ σ, σ.(world) !! int.val a) ≫= unwrap;
        (* TODO: use Sydney's executable version from disk_interpreter.v as
        the generator here *)
      b ← suchThat (gen:=fun _ _ => None) (λ σ b, (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading v _) => Block_to_vals b !! Z.to_nat i = Some v
                | _ => False
                end));
      modify (set world <[ int.val a := b ]>);;
      ret #()
    | SizeOp, LitV LitUnit =>
      sz ← reads (λ σ, disk_size σ.(world));
      ret $ LitV $ LitInt (word.of_Z sz)
    | _, _ => undefined
    end.

  (* these instances are also local (to the outer section) *)
  Instance disk_semantics : ext_semantics disk_op disk_model :=
    { ext_step := ext_step;
      ext_crash := eq; }.

  Program Instance disk_interp: ffi_interp disk_model :=
    {| ffiG := diskG;
       ffi_names := gen_heap_names;
       ffi_get_names := fun _ hD => gen_heapG_get_names (diskG_gen_heapG);
       ffi_update := fun _ hD names =>
                       {| diskG_gen_heapG := gen_heapG_update (@diskG_gen_heapG _ hD) names |};
       ffi_get_update := fun _ _ => _;
       ffi_ctx := fun _ _ (d: @ffi_state disk_model) => gen_heap_ctx d;
       ffi_start := fun _ _ (d: @ffi_state disk_model) =>
                      ([∗ map] l↦v ∈ d, (mapsto (L:=Z) (V:=Block) l 1 v))%I;
       ffi_restart := fun _ _ (d: @ffi_state disk_model) => True%I |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.

  Section proof.
  Context `{!heapG Σ}.
  Instance diskG0 : diskG Σ := heapG_ffiG.

  Notation "l d↦{ q } v" := (mapsto (L:=Z) (V:=Block) l q v%V)
                             (at level 20, q at level 50, format "l  d↦{ q }  v") : bi_scope.
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
        | H : head_step ?e _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Theorem read_fresh : forall σ a b,
      let l := fresh_locs (dom (gset loc) (heap σ)) in
      σ.(world) !! int.val a = Some b ->
      relation.denote (ext_step ReadOp (LitV $ LitInt a)) σ (state_insert_list l (Block_to_vals b) σ) (LitV $ LitLoc $ l).
  Proof.
    intros.
    simpl.
    monad_simpl.
    rewrite H; simpl.
    monad_simpl.
    econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
    apply relation.bind_runF.
    econstructor; eauto.
  Qed.

  Hint Resolve read_fresh : core.
  Hint Extern 1 (head_step (ExternalOp _ _) _ _ _ _ _) => econstructor; simpl : core.

  Definition mapsto_block (l: loc) (q: Qp) (b: Block) :=
    ([∗ map] l ↦ v ∈ heap_array l (fmap Free $ Block_to_vals b), l ↦{q} v)%I.

  Lemma wp_ReadOp s E (a: u64) q b :
    {{{ ▷ int.val a d↦{q} b }}}
      ExternalOp ReadOp (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); int.val a d↦{q} b ∗
                                  mapsto_block l 1 b ∗
                                  [∗ map] l ↦ _ ∈ heap_array l (fmap Free $ Block_to_vals b), meta_token l ⊤ }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ". iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 κ κs n) "(Hσ&Hκs&Hd&Htr) !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _; simpl.
      rewrite /head_step /=.
      monad_simpl.
      rewrite H; simpl.
      monad_simpl.
      econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
      monad_simpl. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    monad_inv.
    simpl in H0.
    rewrite H /= in H0; monad_inv.
    iMod (gen_heap_alloc_gen _ (heap_array l (map Free $ Block_to_vals b)) with "Hσ")
      as "(Hσ & Hl & Hm)".
    { apply heap_array_map_disjoint.
      rewrite map_length length_Block_to_vals; eauto. }
    iModIntro; iSplit; first done.
    iFrame "Hσ Hκs Hd Htr". iApply "HΦ".
    iFrame.
  Qed.

  Definition bindex_of_Z (i: Z) (Hlow: (0 <= i)%Z) (Hhi: (i < 4096)%Z) : fin block_bytes.
    cut (Z.to_nat i < 4096)%nat.
    { apply fin_of_nat. }
    change 4096%nat with (Z.to_nat 4096%Z).
    abstract (apply Z2Nat.inj_lt; auto; vm_compute; inversion 1).
  Defined.

  Theorem block_byte_index {ext: ext_op} (b: Block) (i: Z) (Hlow: (0 <= i)%Z) (Hhi: (i < 4096)%Z) :
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
    (mapsto_block l q b -∗ ∃ v, (l +ₗ i) ↦{q} Free v ∗ ⌜Block_to_vals b !! Z.to_nat i = Some v⌝)%I.
  Proof.
    unfold mapsto_block; intros Hlow Hhi.
    iIntros "Hm".
    pose proof (block_byte_index b i ltac:(auto) ltac:(auto)) as Hi.
    assert (heap_array l (fmap Free $ Block_to_vals b) !! (l +ₗ i) =
            Some $ Free $ LitV $ LitByte $ b !!! bindex_of_Z i Hlow Hhi) as Hha.
    { apply heap_array_lookup.
      eexists; intuition eauto.
      rewrite list_lookup_fmap.
      rewrite Hi; simpl; auto. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hha with "Hm") as "(Hmi&_)".
    iExists _.
    iFrame "Hmi".
    destruct_with_eqn (Block_to_vals b !! Z.to_nat i); auto.
  Qed.

  Theorem heap_valid_block l b q σ :
    gen_heap_ctx σ -∗ mapsto_block l q b -∗
    ⌜ (forall (i:Z), (0 <= i)%Z -> (i < 4096)%Z ->
                match σ !! (l +ₗ i) with
             | Some (Reading v _) => Block_to_vals b !! Z.to_nat i = Some v
             | _ => False
                end) ⌝.
  Proof.
    iIntros "Hσ Hm".
    iIntros (i Hbound1 Hbound2).
    iDestruct (mapsto_block_extract i with "Hm") as (v) "[Hi %]"; eauto.
    iDestruct (@gen_heap_valid with "Hσ Hi") as %?.
    iPureIntro.
    rewrite H0; auto.
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
    {{{ ▷ ∃ b0, int.val a d↦{1} b0 ∗ mapsto_block l q b }}}
      ExternalOp WriteOp (Val $ PairV (LitV $ LitInt a) (LitV $ LitLoc l)) @ s; E
    {{{ RET LitV LitUnit; int.val a d↦{1} b ∗ mapsto_block l q b}}}.
  Proof.
    iIntros (Φ) ">H Hϕ". iDestruct "H" as (b0) "(Ha&Hl)".
    iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 κ κs n) "(Hσ&Hκs&Hd&Htr) !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iDestruct (heap_valid_block with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _; cbn.
      repeat (monad_simpl; cbn).
      rewrite H; cbn; monad_simpl.
      econstructor; eauto; [ | monad_simpl ].
      econstructor; eauto. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    monad_inv.
    rewrite H /= in H1; monad_inv.
    iMod (@gen_heap_update with "Hd Ha") as "[$ Ha]".
    assert (b = b1); [ | subst b1 ].
    { apply Block_to_vals_ext_eq; intros.
      specialize (H0 i); specialize (H2 i); intuition.
      simpl in H4.
      destruct_with_eqn (σ1.(heap) !! (l +ₗ i)); try contradiction.
      destruct n0; try contradiction.
      congruence. }
    iModIntro; iSplit; first done.
    iFrame.
    iApply ("Hϕ" with "[$]").
  Qed.

  Definition disk_array (l: Z) (q: Qp) (vs: list Block): iProp Σ :=
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

  Lemma update_disk_array (l: Z) bs (z: Z) b q :
    0 <= z ->
    bs !! Z.to_nat z = Some b →
    disk_array l q bs -∗ ((l + z) d↦{q} b ∗
                          ∀ b', (l + z) d↦{q} b' -∗
                                                disk_array l q (<[Z.to_nat z:=b']>bs))%I.
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
    rewrite drop_insert; last by lia.
    rewrite Z2Nat.id; auto. iFrame.
  Qed.

  End proof.

End disk.

Global Opaque Write Read Size.
Hint Resolve Write_t Read_t Size_t : types.

Notation "l d↦{ q } v" := (mapsto (L:=Z) (V:=Block) l q%Qp v%V)
                            (at level 20, q at level 50, format "l  d↦{ q }  v") : bi_scope.
Notation "l d↦ v" := (mapsto (L:=Z) (V:=Block) l 1%Qp v%V)
                       (at level 20, format "l  d↦  v") : bi_scope.
Notation "l d↦∗ vs" := (disk_array l 1%Qp vs%V)
                       (at level 20, format "l  d↦∗  vs") : bi_scope.
