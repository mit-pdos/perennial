From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.

From Perennial.go_lang Require Import lang lifting slice typing.

(* this is purely cosmetic but it makes printing line up with how the code is
usually written *)
Set Printing Projections.

Inductive DiskOp := ReadOp | WriteOp | SizeOp.
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  intros x y; hnf; decide equality.
Defined.

Instance DiskOp_fin : Countable DiskOp.
Proof.
  refine (countable.inj_countable'
            (fun op => match op with
                 | ReadOp => 0
                 | WriteOp => 1
                 | SizeOp => 2
                    end)
            (fun n => match n with
                | 0 => ReadOp
                | 1 => WriteOp
                | _ => SizeOp
                   end) _); by intros [].
Qed.

Definition disk_op : ext_op.
Proof.
  refine (mkExtOp DiskOp _ _).
Defined.

Definition disk_ty: ext_types disk_op :=
  {| get_ext_tys (op: @external disk_op) :=
       match op with
    | ReadOp => (uint64T, arrayT byteT)
    | WriteOp => (prodT uint64T (arrayT byteT), unitT)
    | SizeOp => (unitT, uint64T)
       end; |}.

Definition block_bytes: nat := N.to_nat 4096.
Definition BlockSize {ext: ext_op}: val := #4096.
Definition Block := vec byte block_bytes.
Definition blockT: ty := slice.T byteT.

Definition disk_state := gmap Z Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state _).
Defined.

Definition Block_to_vals {ext: ext_op} (bl:Block) : list val :=
  fmap (λ b, LitV $ LitByte b) (vec_to_list bl).

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

  Definition Size: val :=
    λ: <>,
       ExternalOp SizeOp #().

  Theorem Size_t : ⊢ Size : (unitT -> uint64T).
  Proof.
    typecheck.
  Qed.

  Inductive ext_step : DiskOp -> val -> state -> val -> state -> Prop :=
  | ReadOpS : forall (a: u64) (b: Block) (σ: state) l',
      σ.(world) !! int.val a = Some b ->
      (forall (i:Z), 0 <= i -> i < 4096 -> σ.(heap) !! (l' +ₗ i) = None)%Z ->
      ext_step ReadOp (LitV (LitInt a)) σ (LitV (LitLoc l'))
               (state_insert_list l' (Block_to_vals b) σ)
  | WriteOpS : forall (a: u64) (l: loc) (b0 b: Block) (σ: state),
      is_Some (σ.(world) !! int.val a) ->
      (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
             | Some (Free v) => Block_to_vals b !! Z.to_nat i = Some v
             | _ => False
                end)%Z ->
      ext_step WriteOp (PairV (LitV (LitInt a)) (LitV (LitLoc l))) σ
               (LitV LitUnit) (set world <[ int.val a := b ]> σ)
  (* TODO: size semantics *)
  .

  Hint Constructors ext_step : core.

  (* these instances are also local (to the outer section) *)
  Instance disk_semantics : ext_semantics disk_op disk_model :=
    { ext_step := ext_step;
      ext_crash := eq;
      ext_close := eq; }.

  Instance disk_interp: ffi_interp disk_model :=
    {| ffiG := diskG;
       ffi_ctx := fun _ _ (d: @ffi_state disk_model) => gen_heap_ctx d; |}.

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
      ext_step ReadOp (LitV $ LitInt a) σ (LitV $ LitLoc $ l) (state_insert_list l (Block_to_vals b) σ).
  Proof.
    intros.
    constructor; auto; intros.
    apply (not_elem_of_dom (D := gset loc)).
      by apply fresh_locs_fresh.
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
    iIntros (σ1 κ κs n) "(Hσ&Hκs&Hd) !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _; simpl.
      econstructor; simpl.
      apply read_fresh; eauto. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_heap_alloc_gen _ (heap_array l' (map Free $ Block_to_vals b)) with "Hσ")
      as "(Hσ & Hl & Hm)".
    { apply heap_array_map_disjoint.
      rewrite map_length length_Block_to_vals; eauto. }
    iModIntro; iSplit; first done.
    iFrame "Hσ Hκs Hd". iApply "HΦ".
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
             | Some (Free v) => Block_to_vals b !! Z.to_nat i = Some v
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
    iIntros (σ1 κ κs n) "(Hσ&Hκs&Hd) !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iDestruct (heap_valid_block with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro.
      eexists _, _, _, _; simpl.
      econstructor; simpl.
      (* TODO: for some reason eauto doesn't apply this *)
      eapply WriteOpS; eauto. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hd Ha") as "[$ Ha]".
    assert (b = b2); [ | subst b2 ].
    { apply Block_to_vals_ext_eq; intros.
      specialize (H0 i); specialize (H4 i); intuition.
      destruct_with_eqn (σ1.(heap) !! (l +ₗ i)); try contradiction.
      destruct n0; try contradiction.
      congruence. }
    iModIntro; iSplit; first done.
    iFrame.
    iApply "Hϕ".
    iFrame.
  Qed.

  Definition disk_array (l: Z) (q: Qp) (vs: list Block): iProp Σ :=
    ([∗ list] i ↦ b ∈ vs, (l + i) d↦{q} b)%I.

  Theorem disk_array_app l q vs1 vs2 :
    disk_array l q (vs1 ++ vs2) ⊣⊢
               disk_array l q vs1 ∗ disk_array (l + length vs1) q vs2.
  Proof.
    rewrite /disk_array big_sepL_app.
    setoid_rewrite Nat2Z.inj_add.
    by setoid_rewrite Z.add_assoc.
  Qed.

  Theorem disk_array_split l q z vs :
    0 <= z <= Z.of_nat (length vs) ->
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
