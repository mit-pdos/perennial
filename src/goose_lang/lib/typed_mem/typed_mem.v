From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang.lib Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Export typed_mem.impl.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
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

  Definition struct_pointsto_def l (dq:dfrac) (t:ty) (v: val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{dq} vj) ∗ ⌜val_ty v t⌝)%I.
  Definition struct_pointsto_aux : seal (@struct_pointsto_def). Proof. by eexists. Qed.
  Definition struct_pointsto := struct_pointsto_aux.(unseal).
  Definition struct_pointsto_eq : @struct_pointsto = @struct_pointsto_def := struct_pointsto_aux.(seal_eq).

  Notation "l ↦[ t ]{# q } v" := (struct_pointsto l (DfracOwn q) t v%V)
                                   (at level 20, q at level 50, t at level 50,
                                    format "l  ↦[ t ]{# q }  v") : bi_scope.
  Notation "l ↦[ t ]□ v" := (struct_pointsto l DfracDiscarded t v%V)
                                   (at level 20, t at level 50,
                                    format "l  ↦[ t ]□  v") : bi_scope.
  Notation "l ↦[ t ]{ dq } v" := (struct_pointsto l dq t v%V)
                                   (at level 20, dq at level 50, t at level 50,
                                    format "l  ↦[ t ]{ dq }  v") : bi_scope.
  Notation "l ↦[ t ] v" := (struct_pointsto l (DfracOwn 1) t v%V)
                              (at level 20, t at level 50,
                               format "l  ↦[ t ]  v") : bi_scope.

  Ltac unseal := rewrite ?struct_pointsto_eq /struct_pointsto_def.

  Global Instance struct_pointsto_timeless l t q v: Timeless (l ↦[t]{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance struct_pointsto_fractional l t v: fractional.Fractional (λ q, l ↦[t]{#q} v)%I.
  Proof. unseal. apply _. Qed.

  Theorem struct_pointsto_singleton l q t v v0 :
    flatten_struct v = [v0] ->
    l ↦[t]{q} v ⊢@{_} l ↦{q} v0.
  Proof.
    intros Hv.
    unseal.
    rewrite Hv /=.
    rewrite loc_add_0 right_id.
    by iIntros "[$ _]".
  Qed.

  Theorem struct_pointsto_ty q l v t :
    l ↦[t]{q} v ⊢@{_} ⌜val_ty v t⌝.
  Proof.
    unseal. iIntros "[_ %] !%//".
  Qed.

  Theorem struct_pointsto_frac_valid l q t v :
    0 < ty_size t →
    l ↦[t]{#q} v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    unseal.
    iIntros (?) "[Hvals %Hval_ty]".
    apply val_ty_len in Hval_ty.
    destruct (flatten_struct v); simpl in *.
    - lia.
    - iDestruct "Hvals" as "[Hl _]".
      iDestruct (heap_pointsto_frac_valid with "Hl") as %Hq.
      auto.
  Qed.

  Local Lemma struct_pointsto_agree_flatten l t q1 v1 q2 v2 :
    length (flatten_struct v1) = length (flatten_struct v2) ->
    l ↦[t]{q1} v1 -∗ l ↦[t]{q2} v2 -∗
    ⌜flatten_struct v1 = flatten_struct v2⌝.
  Proof.
    unseal.
    iIntros (Hlen) "[Hl1 _] [Hl2 _]".
    generalize dependent (flatten_struct v1); intros l1.
    generalize dependent (flatten_struct v2); intros l2.
    clear.
    iIntros (Hlen).
    (iInduction l1 as [|v1 l1] "IH" forall (l l2 Hlen)).
    { simpl in Hlen.
      destruct l2; simpl in Hlen; try congruence.
      auto. }
    destruct l2; simpl in Hlen; try congruence.
    simpl.
    iDestruct "Hl1" as "[Hx1 Hl1]".
    iDestruct "Hl2" as "[Hx2 Hl2]".
    iDestruct (heap_pointsto_agree with "[$Hx1 $Hx2]") as "->".
    setoid_rewrite loc_add_Sn.
    iDestruct ("IH" $! (l +ₗ 1) l2 with "[] Hl1 Hl2") as %->; auto.
  Qed.

  Theorem struct_pointsto_agree l t q1 v1 q2 v2 :
    l ↦[t]{q1} v1 -∗ l ↦[t]{q2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (struct_pointsto_ty with "Hl1") as %Hty1.
    iDestruct (struct_pointsto_ty with "Hl2") as %Hty2.
    pose proof (val_ty_len Hty1).
    pose proof (val_ty_len Hty2).
    iDestruct (struct_pointsto_agree_flatten with "Hl1 Hl2") as %Heq.
    { congruence. }
    iPureIntro.
    eapply flatten_struct_inj; eauto.
  Qed.

  Global Instance struct_pointsto_persistent l t v : Persistent (l ↦[t]□ v).
  Proof. rewrite struct_pointsto_eq. apply _. Qed.

  Lemma struct_pointsto_persist l dq t v:
    l ↦[t]{dq} v ==∗ l ↦[t]□ v.
  Proof.
    rewrite struct_pointsto_eq /struct_pointsto_def.
    iIntros "[Ha %Ht]".
    iDestruct (big_sepL_mono with "Ha") as "Ha".
    2: iMod (big_sepL_bupd with "Ha") as "Ha".
    { iIntros (???) "H".
      iMod (heap_pointsto_persist with "H") as "H". iModIntro. iExact "H". }
    iModIntro. iFrame "Ha". done.
  Qed.

  Lemma byte_pointsto_untype l q (x: u8) :
    l ↦[byteT]{q} #x ⊣⊢ l ↦{q} #x.
  Proof.
    rewrite struct_pointsto_eq /struct_pointsto_def /=.
    rewrite loc_add_0 right_id.
    iSplit.
    - iDestruct 1 as "[$ _]".
    - iDestruct 1 as "$".
      auto.
  Qed.

  Theorem base_pointsto_untype {l bt q v} :
    match bt with
    | unitBT => false
    | _ => true
    end = true ->
    l ↦[baseT bt]{q} v ⊣⊢ l ↦{q} v ∗ ⌜val_ty v (baseT bt)⌝.
  Proof.
    intros Hnotunit.
    iSplit.
    - iIntros "Hl".
      iDestruct (struct_pointsto_ty with "Hl") as %Hty.
      rewrite struct_pointsto_singleton; eauto.
      inv_ty; simpl; auto.
      congruence.
    - iIntros "[Hl %]".
      unseal.
      iSplitL; auto.
      inv_ty; simpl; try rewrite loc_add_0 right_id; auto.
  Qed.

  Theorem base_load_ty {bt} :
    match bt with
    | unitBT => false
    | _ => true
    end = true ->
    load_ty (baseT bt) = (λ: "l", !(Var "l"))%V.
  Proof.
    destruct bt; simpl; intros; auto.
    congruence.
  Qed.

  Theorem wp_base_load stk E bt (l:loc) (Φ: val -> iProp Σ) :
    match bt with
    | unitBT => false
    | _ => true
    end = true ->
    (∀ le, ⌜Atomic StronglyAtomic le⌝ -∗
           (∀ q v,
               {{{ l ↦[baseT bt]{q} v }}}
                 le @ stk; E
               {{{ RET v; l ↦[baseT bt]{q} v }}}) -∗
           WP le @ stk; E {{ Φ }}) -∗
    WP load_ty (baseT bt) #l @ stk; E {{ Φ }}.
  Proof.
    intros Hnotunit.
    iIntros "Hle".
    rewrite -> base_load_ty by auto.
    wp_lam.
    iApply "Hle".
    { iPureIntro.
      apply _. }
    iIntros (q v Φ') "!> Hl HΦ'".
    iDestruct (struct_pointsto_ty with "Hl") as %Hty.
    iDestruct (base_pointsto_untype with "Hl") as "[Hl _]"; auto.
    wp_apply (wp_load with "Hl").
    iIntros "Hl".
    iApply "HΦ'".
    iApply (base_pointsto_untype with "[$Hl]"); eauto.
  Qed.

  Theorem struct_pointsto_prod q l v1 t1 v2 t2 :
    l ↦[t1 * t2]{q} (v1, v2) ⊣⊢ l ↦[t1]{q} v1 ∗ (l +ₗ ty_size t1) ↦[t2]{q} v2.
  Proof.
    unseal.
    rewrite /struct_pointsto /= big_opL_app.
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

  Theorem nat_scaled_offset_to_Z {v t} {i: nat} :
    val_ty v t ->
    Z.of_nat (length (flatten_struct v)) * i =
    ty_size t * Z.of_nat i.
  Proof.
    intros Hty.
    rewrite (val_ty_len Hty).
    pose proof (ty_size_ge_0 t).
    rewrite Z2Nat.id; auto.
  Qed.

  (* this is the core reasoning, not intended for external use *)
  Local Theorem wp_AllocAt t stk E v :
    val_ty v t ->
    {{{ True }}}
      ref v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_apply wp_allocN_seq; first by word.
    change (uint.nat 1) with 1%nat; simpl.
    iIntros (l) "[Hl _]".
    iApply "HΦ".
    unseal.
    iSplitL; auto.
    rewrite Z.mul_0_r loc_add_0.
    iFrame.
  Qed.

  Theorem wp_ref_to t stk E v :
    val_ty v t ->
    {{{ True }}}
      ref_to t v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_call.
    wp_apply (wp_AllocAt t); auto.
  Qed.

  (* TODO: this is only because Goose doesn't use ref_zero *)
  Theorem wp_ref_of_zero stk E t :
    has_zero t ->
    {{{ True }}}
      ref (zero_val t) @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Hzero Φ) "_ HΦ".
    wp_apply (wp_AllocAt t); eauto.
  Qed.

  Theorem wp_ref_zero stk E t :
    has_zero t ->
    {{{ True }}}
      ref_zero t #() @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Hzero Φ) "_ HΦ".
    wp_call.
    wp_apply wp_ref_of_zero; eauto.
  Qed.

  Theorem wp_LoadAt stk E q l t v :
    {{{ ▷ l ↦[t]{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET v; l ↦[t]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %]".
    hnf in H.
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦{q} vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    (* TODO: we have to rename this so it doesn't conflict with a name generated
  by induction; seems like a bug *)
    rename l into l'.
    (iInduction H as [ | | | | | | | | ] "IH" forall (l' Φ));
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
      by iFrame.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
    - wp_apply (wp_load with "[$]"); auto.
  Qed.

  Lemma tac_wp_load_ty Δ Δ' s E i K l q t v Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, struct_pointsto l q t v)%I →
    envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ???.
    rewrite -wp_bind. eapply bi.wand_apply; first by apply bi.wand_entails, wp_LoadAt.
    rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
    by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

  Theorem wp_store stk E l v v' :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /Store.
    wp_apply (wp_prepare_write with "Hl"); iIntros "[Hl Hl']".
    by wp_apply (wp_finish_store with "[$Hl $Hl']").
  Qed.

  Theorem wp_StoreAt stk E l t v0 v :
    val_ty v t ->
    {{{ ▷ l ↦[t] v0 }}}
      (#l <-[t] v)%V @ stk; E
    {{{ RET #(); l ↦[t] v }}}.
  Proof.
    intros Hty.
    unseal.
    iIntros (Φ) ">[Hl %] HΦ".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦ vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    rename v into v'.
    rename l into l'.
    (iInduction H as [ | | | | | | | | ] "IH" forall (v' Hty l' Φ));
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

  Lemma tac_wp_store_ty Δ Δ' Δ'' stk E i K l t v v' Φ :
    val_ty v' t ->
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦[t] v)%I →
    envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
    envs_entails Δ (WP fill K (store_ty t (PairV (LitV l) v')) @ stk; E {{ Φ }}).
  Proof.
    intros Hty.
    rewrite envs_entails_unseal=> ????.
    rewrite -wp_bind. eapply bi.wand_apply; first by eapply bi.wand_entails, wp_StoreAt.
    rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

End goose_lang.

Notation "l ↦[ t ]{# q } v" := (struct_pointsto l (DfracOwn q) t v%V)
                                 (at level 20, q at level 50, t at level 50,
                                  format "l  ↦[ t ]{# q }  v") : bi_scope.
Notation "l ↦[ t ]□ v" := (struct_pointsto l DfracDiscarded t v%V)
                                 (at level 20, t at level 50,
                                  format "l  ↦[ t ]□  v") : bi_scope.
Notation "l ↦[ t ]{ dq } v" := (struct_pointsto l dq t v%V)
                                 (at level 20, dq at level 50, t at level 50,
                                  format "l  ↦[ t ]{ dq }  v") : bi_scope.
Notation "l ↦[ t ] v" := (struct_pointsto l (DfracOwn 1) t v%V)
                            (at level 20, t at level 50,
                             format "l  ↦[ t ]  v") : bi_scope.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_ty _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'load_ty' in" e];
    [tc_solve
    |solve_pointsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_] _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store_ty _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [val_ty
    |tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
