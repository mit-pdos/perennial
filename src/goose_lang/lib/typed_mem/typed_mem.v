From Perennial.goose_lang Require Import lifting proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.impl.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
  Context {ext_ty: ext_types ext}.

  Ltac invc H := inversion H; subst; clear H.

  Ltac inv_ty :=
    repeat match goal with
           | [ H: val_ty _ ?t |- _ ] =>
             first [ is_var t; fail 1 | invc H ]
           | [ H: lit_ty _ ?t |- _ ] =>
             first [ is_var t; fail 1 | invc H ]
           end.

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

  Theorem struct_mapsto_ty q l v t :
    l ↦[t]{q} v -∗ ⌜val_ty v t⌝.
  Proof.
    iIntros "[_ %] !%//".
  Qed.

  Theorem struct_ptsto_pair_split q l v1 t1 v2 t2 :
    l ↦[t1 * t2]{q} (v1, v2) ⊣⊢ l ↦[t1]{q} v1 ∗ (l +ₗ ty_size t1) ↦[t2]{q} v2.
  Proof.
    rewrite /struct_mapsto /= big_opL_app.
    iSplit.
    - iIntros "[[Hv1 Hv2] %]".
      inversion H; subst; clear H.
      iSplitL "Hv1"; iFrame; eauto.
      iSplitL; eauto.
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
    - iIntros "[[Hv1 %] [Hv2 %]]".
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
      iPureIntro.
      constructor; auto.
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

Notation "l ↦[ ty ]{ q } v" := (struct_mapsto l q ty v%V)
                                 (at level 20, q at level 50, ty at level 50,
                                  format "l  ↦[ ty ]{ q }  v") : bi_scope.
Notation "l ↦[ ty ] v" := (struct_mapsto l 1 ty v%V)
                            (at level 20, ty at level 50,
                             format "l  ↦[ ty ]  v") : bi_scope.
