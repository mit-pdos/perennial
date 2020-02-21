From Perennial.goose_lang Require Export notation typing.
From Perennial.goose_lang Require Import lifting proofmode.
From Perennial.goose_lang.lib Require Import map.impl.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
  Context {ext_ty: ext_types ext}.

  Inductive lit_ty : base_lit -> ty -> Prop :=
  | int_ty x : lit_ty (LitInt x) uint64T
  | int32_ty x : lit_ty (LitInt32 x) uint32T
  | int8_ty x : lit_ty (LitByte x) byteT
  | bool_ty x : lit_ty (LitBool x) boolT
  | string_ty x : lit_ty (LitString x) stringT
  | unit_ty : lit_ty LitUnit unitT
  | loc_array_ty x t : lit_ty (LitLoc x) (arrayT t)
  | loc_struct_ty x ts : lit_ty (LitLoc x) (structRefT ts)
  .

  (* approximate types for closed values *)
  Inductive val_ty : val -> ty -> Prop :=
  | base_ty l t : lit_ty l t -> val_ty (LitV l) t
  | val_ty_pair v1 t1 v2 t2 : val_ty v1 t1 ->
                              val_ty v2 t2 ->
                              val_ty (PairV v1 v2) (prodT t1 t2)
  | sum_ty_l v1 t1 t2 : val_ty v1 t1 ->
                        val_ty (InjLV v1) (sumT t1 t2)
  | sum_ty_r v2 t1 t2 : val_ty v2 t2 ->
                        val_ty (InjRV v2) (sumT t1 t2)
  | map_def_ty v t : val_ty v t ->
                     val_ty (MapNilV v) (mapValT t)
  | map_cons_ty k v mv' t : val_ty mv' (mapValT t) ->
                            val_ty k uint64T ->
                            val_ty v t ->
                            val_ty (InjRV (k, v, mv')%V) (mapValT t)
  | rec_ty f x e t1 t2 : val_ty (RecV f x e) (arrowT t1 t2)
  | ext_def_ty x : val_ty (ExtV (val_ty_def x)) (extT x)
  .

  Theorem zero_val_ty' t : val_ty (zero_val t) t.
  Proof.
    induction t; simpl; eauto using val_ty, lit_ty.
    destruct t; eauto using val_ty, lit_ty.
  Qed.

  Ltac invc H := inversion H; subst; clear H.

  Ltac inv_ty :=
    repeat match goal with
           | [ H: val_ty _ ?t |- _ ] =>
             first [ is_var t; fail 1 | invc H ]
           | [ H: lit_ty _ ?t |- _ ] =>
             first [ is_var t; fail 1 | invc H ]
           end.

  Theorem val_ty_len {v t} :
    val_ty v t ->
    length (flatten_struct v) = Z.to_nat (ty_size t).
  Proof.
    induction 1; simpl; rewrite -> ?app_length in *; auto.
    - invc H; eauto.
    - pose proof (ty_size_ge_0 t1).
      pose proof (ty_size_ge_0 t2).
      lia.
  Qed.

  Theorem val_ty_flatten_length v t :
    val_ty v t ->
    length (flatten_struct v) = length (flatten_ty t).
  Proof.
    induction 1; simpl; auto.
    - invc H; eauto.
    - rewrite ?app_length.
      lia.
  Qed.

  Theorem ty_size_offset t l j :
    l +ₗ (length (flatten_ty t) + j)%nat = l +ₗ ty_size t +ₗ j.
  Proof.
    rewrite loc_add_assoc.
    f_equal.
    rewrite <- ty_size_length.
    pose proof (ty_size_ge_0 t).
    lia.
  Qed.

  Definition struct_mapsto l q (t:ty) (v: val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{q} vj) ∗ ⌜val_ty v t⌝)%I.

  Notation "l ↦[ t ]{ q } v" := (struct_mapsto l q t v%V)
                                   (at level 20, q at level 50, t at level 50,
                                    format "l  ↦[ t ]{ q }  v") : bi_scope.
  Notation "l ↦[ t ] v" := (struct_mapsto l 1 t v%V)
                              (at level 20, t at level 50,
                               format "l  ↦[ t ]  v") : bi_scope.

  Theorem struct_mapsto_singleton l q t v v0 :
    flatten_struct v = [v0] ->
    l ↦[t]{q} v -∗ l ↦{q} v0.
  Proof.
    intros Hv.
    rewrite /struct_mapsto Hv /=.
    rewrite loc_add_0 right_id.
    by iIntros "[$ _]".
  Qed.

  Fixpoint load_ty t: val :=
    match t with
    | prodT t1 t2 => λ: "l", (load_ty t1 (Var "l"), load_ty t2 (Var "l" +ₗ[t1] #1))
    | baseT unitBT => λ: <>, #()
    | _ => λ: "l", !(Var "l")
    end.

  Fixpoint store_ty t: val :=
    match t with
    | prodT t1 t2 => λ: "p" "v",
                    store_ty t1 (Var "p") (Fst (Var "v"));;
                    store_ty t2 (Var "p" +ₗ[t1] #1) (Snd (Var "v"))
    | baseT unitBT => λ: <> <>, #()
    | _ => λ: "p" "v", Var "p" <- Var "v"
    end.

  Lemma wp_LoadAt stk E q l t v :
    {{{ l ↦[t]{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET v; l ↦[t]{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iDestruct "Hl" as "[Hl %]".
    hnf in H.
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦{q} vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    (* TODO: we have to rename this so it doesn't conflict with a name generated
  by induction; seems like a bug *)
    rename l into l'.
    (iInduction H as [ | | | | | | | ] "IH" forall (l' Φ));
      simpl;
      wp_pures;
      rewrite ?loc_add_0 ?right_id.
    - inversion H; subst; simpl;
        rewrite ?loc_add_0 ?right_id;
        try wp_apply (wp_load with "[$]"); auto.
      wp_pures.
      iApply ("HΦ" with "[//]").
    - rewrite big_opL_app.
      iDestruct "Hl" as "[Hv1 Hv2]".
      wp_apply ("IH" with "Hv1"); iIntros "Hv1".
      wp_apply ("IH1" with "[Hv2]"); [ | iIntros "Hv2" ].
      { erewrite val_ty_flatten_length; eauto.
        setoid_rewrite ty_size_offset.
        rewrite Z.mul_1_r.
        iFrame. }
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      rewrite Z.mul_1_r.
      iFrame.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
  Qed.

  Lemma wp_store stk E l v v' :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /Store.
    wp_apply (wp_prepare_write with "Hl"); iIntros "Hl".
    by wp_apply (wp_finish_store with "Hl").
  Qed.

  Lemma wp_StoreAt stk E l t v0 v :
    val_ty v t ->
    {{{ l ↦[t] v0 }}}
      store_ty t #l v @ stk; E
    {{{ RET #(); l ↦[t] v }}}.
  Proof.
    intros Hty.
    iIntros (Φ) "[Hl %] HΦ".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦ vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    rename v into v'.
    rename l into l'.
    (iInduction H as [ | | | | | | | ] "IH" forall (v' Hty l' Φ));
      simpl;
      rewrite ?loc_add_0 ?right_id;
      wp_pures.
    - invc Hty; invc H;
        try match goal with
            | [ H: lit_ty _ _ |- _ ] => invc H
            end;
        simpl;
        rewrite ?loc_add_0 ?right_id;
        try (wp_apply (wp_store with "[$]"); auto).
      wp_pures.
      iApply ("HΦ" with "[//]").
    - rewrite big_opL_app.
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      invc Hty.
      { by invc H1. (* can't be a pair and a base literal *) }
      iDestruct "Hl" as "[Hv1 Hv2]".
      wp_pures.
      wp_apply ("IH" with "[//] Hv1").
      iIntros "Hv1".
      wp_pures.
      rewrite Z.mul_1_r.
      wp_apply ("IH1" with "[//] Hv2").
      iIntros "Hv2".
      iApply "HΦ".
      simpl.
      rewrite big_opL_app.
      iFrame.
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
    - inv_ty;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
    - inv_ty;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
    - invc Hty;
        try match goal with
            | [ H: lit_ty _ _ |- _ ] => invc H
            end;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
    - invc Hty;
        try match goal with
            | [ H: lit_ty _ _ |- _ ] => invc H
            end;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
    - inv_ty;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
    - inv_ty;
        rewrite /= ?loc_add_0 ?right_id;
        wp_apply (wp_store with "[$]"); auto.
  Qed.

End goose_lang.

Ltac val_ty :=
  lazymatch goal with
  | |- val_ty (zero_val _) _ => apply zero_val_ty'
  | [ H: val_ty ?v ?t |- val_ty ?v ?t ] => exact H
  | |- val_ty _ _ => solve [ repeat constructor ]
  | _ => fail "not a val_ty goal"
  end.

Hint Extern 2 (val_ty _ _) => val_ty : core.

Notation "l ↦[ ty ]{ q } v" := (struct_mapsto l q ty v%V)
                                 (at level 20, q at level 50, ty at level 50,
                                  format "l  ↦[ ty ]{ q }  v") : bi_scope.
Notation "l ↦[ ty ] v" := (struct_mapsto l 1 ty v%V)
                            (at level 20, ty at level 50,
                             format "l  ↦[ ty ]  v") : bi_scope.
