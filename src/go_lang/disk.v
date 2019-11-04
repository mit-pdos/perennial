From stdpp Require Import gmap.
From stdpp Require Import vector.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.

From Perennial.go_lang Require Import lang lifting.

Inductive DiskOp := Read | Write.
Instance eq_DiskOp : EqDecision DiskOp.
Proof.
  intros x y; hnf; decide equality.
Defined.

Definition disk_op : ext_op.
Proof.
  unshelve refine (mkExtOp DiskOp _ _).
  - apply _.
  - apply (countable.inj_countable
           (fun op => match op with
                   | Read => 0
                   | Write => 1
                   end)
           (fun n => match n with
                  | 0 => Some Read
                  | 1 => Some Write
                  | _ => None
                  end)).
    destruct x; auto.
Defined.

Definition block_bytes: nat := N.to_nat 4096.
Definition Block := vec byte block_bytes.

Definition Block_map {ext:ext_op} (b:Block) : gmap Z val.
Proof.
Admitted.

Definition disk_state := gmap u64 Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state _).
Defined.

Definition Block_to_vals {ext: ext_op} (bl:Block) : list val :=
  map (λ b, LitV (LitByte b)) (vec_to_list bl).

Lemma length_Block_to_vals {ext: ext_op} b :
    length (Block_to_vals b) = block_bytes.
Proof.
  unfold Block_to_vals.
  rewrite map_length.
  rewrite vec_to_list_length.
  reflexivity.
Qed.

Class diskG Σ :=
  { diskG_gen_heapG :> gen_heapG u64 Block Σ; }.

Section disk.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model.

  Definition state_insert_block (l: loc) (b: Block) (σ: state): state :=
    state_upd_heap (λ h, heap_array l (Block_to_vals b) ∪ h) σ.

  Inductive ext_step : DiskOp -> val -> state -> val -> state -> Prop :=
  | ReadS : forall (a: u64) (b: Block) (σ: state) l',
      σ.(world) !! a = Some b ->
      (forall (i:Z), 0 <= i -> i < 4096 -> σ.(heap) !! (l' +ₗ i) = None)%Z ->
      ext_step Read (LitV (LitInt a)) σ (LitV (LitLoc l'))
               (state_insert_block l' b σ)
  | WriteS : forall (a: u64) (l: loc) (b0 b: Block) (σ: state),
      σ.(world) !! a = Some b0 ->
      (forall (i:Z), 0 <= i -> i < 4096 ->
                σ.(heap) !! (l +ₗ i) =
                Block_to_vals b !! Z.to_nat i)%Z ->
      ext_step Write (PairV (LitV (LitInt a)) (LitV (LitLoc l))) σ
               (LitV LitUnit) (state_upd_world <[ a := b ]> σ)

  .

  Hint Constructors ext_step : core.

  (* these instances are also local (to the outer section) *)
  Instance disk_semantics : ext_semantics disk_op disk_model :=
    { ext_step := ext_step; }.

  Instance disk_interp: ffi_interp disk_model :=
    {| ffiG := diskG;
       ffi_ctx := fun _ _ (d: @ffi_state disk_model) => gen_heap_ctx d; |}.

  Section proof.
  Context `{!heapG Σ}.
  Instance diskG0 : diskG Σ := heapG_ffiG.

  Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
                             (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
  Notation "l d↦{ q } v" := (mapsto (L:=u64) (V:=Block) l q v%V)
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
      σ.(world) !! a = Some b ->
      ext_step Read (LitV $ LitInt a) σ (LitV $ LitLoc $ l) (state_insert_block l b σ).
  Proof.
    intros.
    constructor; auto; intros.
    apply (not_elem_of_dom (D := gset loc)).
      by apply fresh_locs_fresh.
  Qed.

  Hint Resolve read_fresh : core.
  Hint Extern 1 (head_step (ExternalOp _ _) _ _ _ _ _) => econstructor; simpl : core.

  Lemma wp_Read s E a q b :
    {{{ ▷ a d↦{q} b }}}
      ExternalOp Read (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); a d↦{q} b ∗
                                  [∗ map] l ↦ v ∈ heap_array l (Block_to_vals b), l ↦{1} v ∗
                                  meta_token l ⊤ }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n) "(Hσ&Hκs&Hd) !>".
    cbv [ffi_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_heap_alloc_gen _ (heap_array l' (Block_to_vals b)) with "Hσ")
    as "(Hσ & Hl & Hm)".
    { apply heap_array_map_disjoint.
      rewrite length_Block_to_vals; eauto. }
  iModIntro; iSplit; first done.
  iFrame "Hσ Hκs Hd". iApply "HΦ".
  iFrame "Ha".
  iApply big_sepM_sep. iFrame.
  Qed.
  End proof.

End disk.
