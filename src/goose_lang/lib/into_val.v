From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang.lib Require Import typed_mem slice.slice struct.struct.

Class IntoVal {ext: ext_op} V :=
  { to_val: V -> val;
    IntoVal_def: V;
    IntoVal_eq: ∀ v v', to_val v = to_val v' -> v = v'
  }.

Class IntoValForType {ext V} (H: @IntoVal ext V) {ext_ty: ext_types ext} (t:ty) :=
    { def_is_zero: to_val IntoVal_def = zero_val t;
      to_val_has_zero: has_zero t;
      (* TODO: this isn't necessary, but it seems reasonable *)
      to_val_ty: forall v, val_ty (to_val v) t; }.

Theorem IntoVal_eq_fmap_list {ext V} (H: @IntoVal ext V) :
  ∀ (l l' : list V),
  to_val <$> l = to_val <$> l' ->
  l = l'.
Proof.
  induction l; intros.
  - destruct l'; simpl in *; congruence.
  - destruct l'; simpl in *; try congruence.
    inversion H0.
    erewrite IHl; eauto.
    eapply IntoVal_eq in H2; subst; eauto.
Qed.

Theorem IntoVal_eq_fmap_list_permutation {ext V} (H: @IntoVal ext V) :
  ∀ (l l' : list V),
  to_val <$> l ≡ₚ to_val <$> l' ->
  l ≡ₚ l'.
Proof.
  induction l; intros.
  - destruct l'; simpl in *; eauto.
    exfalso. eapply Permutation_nil_cons. eauto.
  - rewrite fmap_cons in H0. symmetry in H0.
    eapply Permutation_cons_inv in H0.
    destruct H0 as [l0' [l1' ?]]; intuition idtac.
    eapply fmap_app_inv in H1.
    destruct H1 as [l0 [l1 ?]]; intuition idtac. subst.
    destruct l1; first by simpl in *; congruence.
    rewrite fmap_cons in H0. inversion H0; clear H0.
    eapply IntoVal_eq in H3; subst.
    eapply Permutation_cons_app.
    eapply IHl. rewrite fmap_app. eauto.
Qed.

Theorem IntoVal_eq_fmap_prod_permutation {ext V} (H: @IntoVal ext V) {K} :
  ∀ (l l' : list (K * V)),
  prod_map id to_val <$> l ≡ₚ prod_map id to_val <$> l' ->
  l ≡ₚ l'.
Proof.
  induction l; intros.
  - destruct l'; simpl in *; eauto.
    exfalso. eapply Permutation_nil_cons. eauto.
  - rewrite fmap_cons in H0. symmetry in H0.
    eapply Permutation_cons_inv in H0.
    destruct H0 as [l0' [l1' ?]]; intuition idtac.
    eapply fmap_app_inv in H1.
    destruct H1 as [l0 [l1 ?]]; intuition idtac. subst.
    destruct l1; first by simpl in *; congruence.
    rewrite fmap_cons in H0. inversion H0; clear H0.
    eapply IntoVal_eq in H4; subst.
    destruct a, p; simpl in *; subst.
    eapply Permutation_cons_app.
    eapply IHl. rewrite fmap_app. eauto.
Qed.

Theorem IntoVal_eq_fmap_map {ext V K} (H: @IntoVal ext V) `{Countable K}:
  ∀ (m m' : gmap K V),
  to_val <$> m = to_val <$> m' ->
  m = m'.
Proof.
  intros.
  rewrite <- (list_to_map_to_list m) in *.
  rewrite <- (list_to_map_to_list m') in *.
  pose proof (NoDup_fst_map_to_list m).
  pose proof (NoDup_fst_map_to_list m').
  generalize dependent (map_to_list m).
  generalize dependent (map_to_list m').
  intros.
  eapply list_to_map_proper; eauto.
  rewrite -?list_to_map_fmap in H1.
  eapply IntoVal_eq_fmap_prod_permutation.
  eapply list_to_map_inj in H1; eauto.
  { rewrite -list_fmap_compose /compose /prod_map /=. eauto. }
  { rewrite -list_fmap_compose /compose /prod_map /=. eauto. }
Qed.

(** instances for IntoVal *)
Section instances.
  Context {ext: ext_op} {ext_ty: ext_types ext}.
  Global Instance u64_IntoVal : IntoVal u64 :=
    {| to_val := λ (x: u64), #x;
       IntoVal_def := U64 0;
       IntoVal_eq := ltac:(congruence) |}.

  Global Instance u64_IntoVal_uint64T : IntoValForType u64_IntoVal uint64T.
  Proof.
    constructor; auto.
  Qed.

  Global Instance u8_IntoVal : IntoVal u8 :=
    {| to_val := λ (x: u8), #x;
       IntoVal_def := U8 0;
       IntoVal_eq := ltac:(congruence) |}.

  Global Instance u8_IntoVal_byteT : IntoValForType u8_IntoVal byteT.
  Proof.
    constructor; eauto.
  Qed.

  Global Instance loc_IntoVal : IntoVal loc :=
    {| to_val := λ (l: loc), #l;
       IntoVal_def := null;
       IntoVal_eq := ltac:(congruence)
    |}.

  Global Instance loc_IntoVal_struct_ptr t : IntoValForType loc_IntoVal (struct.ptrT t).
  Proof.
    constructor; auto.
  Qed.

  Global Instance loc_IntoVal_ref t : IntoValForType loc_IntoVal (refT t).
  Proof.
    constructor; auto.
  Qed.

  Global Instance slice_IntoVal : IntoVal Slice.t.
    refine
    {| to_val := slice_val;
       IntoVal_def := Slice.nil;
       IntoVal_eq := _
    |}.
    destruct v, v'.
    rewrite /slice_val /=.
    intro H; inversion H; eauto.
  Defined.

  Global Instance slice_IntoVal_ref t : IntoValForType slice_IntoVal (slice.T t).
  Proof.
    constructor; auto.
    intros.
    apply slice_val_ty.
  Qed.

End instances.
