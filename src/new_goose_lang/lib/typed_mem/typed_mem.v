From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang Require Export typed_mem.impl struct.impl slice.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Inductive has_go_abstract_type : val → go_abstract_type → Prop :=
  | has_go_abstract_type_bool (b : bool) : has_go_abstract_type #b cellT
  | has_go_abstract_type_uint64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_uint32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_uint16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_uint8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_int16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_int8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_string (x : string) : has_go_abstract_type #(str x) cellT
  | has_go_abstract_type_ptr (x : loc) : has_go_abstract_type #x cellT
  | has_go_abstract_type_func f x e : has_go_abstract_type (RecV f x e) cellT
  | has_go_abstract_type_nil : has_go_abstract_type nil cellT
  | has_go_abstract_type_unit : has_go_abstract_type #() unitT
  | has_go_abstract_type_prod
      (v1 v2 : val) (t1 t2 : go_abstract_type)
      (Ht1 : has_go_abstract_type v1 t1)
      (Ht2 : has_go_abstract_type v2 t2)
    : has_go_abstract_type (v1, v2) (prodT t1 t2)
  .

  Existing Class has_go_abstract_type.
  Existing Instance has_go_abstract_type_uint8.
  Existing Instance has_go_abstract_type_bool.
  Existing Instance has_go_abstract_type_uint64.
  Existing Instance has_go_abstract_type_uint32.
  (* Existing Instance  | has_go_abstract_type_uint16 (x : w16) : has_go_abstract_type #x cellT *)
  Existing Instance has_go_abstract_type_uint8.
  Existing Instance has_go_abstract_type_int64.
  Existing Instance has_go_abstract_type_int32.
  (* Existing Instance  | has_go_abstract_type_int16 (x : w16) : has_go_abstract_type #x cellT *)
  Existing Instance has_go_abstract_type_int8.
  Existing Instance has_go_abstract_type_string.
  Existing Instance has_go_abstract_type_ptr.
  Existing Instance has_go_abstract_type_func.
  Existing Instance has_go_abstract_type_nil.
  Existing Instance has_go_abstract_type_unit.
  Existing Instance has_go_abstract_type_prod.

  Definition has_go_type (v : val) (t : go_type) := has_go_abstract_type v (go_type_interp t).


  Ltac invc H := inversion H; subst; clear H.

  Ltac inv_ty :=
    repeat match goal with
           | [ H: has_go_type _ ?t |- _ ] =>
             first [ is_var t; fail 1 | invc H ]
           end.

  Lemma ty_size_offset t l j :
    l +ₗ (length (flatten_ty t) + j)%nat = l +ₗ ty_size t +ₗ j.
  Proof.
    rewrite loc_add_assoc.
    f_equal.
    rewrite <- ty_size_length.
    pose proof (ty_size_ge_0 t).
    lia.
  Qed.

  Definition typed_pointsto_def l (dq : dfrac) (t : go_type) (v : val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{dq} vj) ∗ ⌜ has_go_type v t ⌝)%I.
  Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
  Definition typed_pointsto := typed_pointsto_aux.(unseal).
  Definition typed_pointsto_eq : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).

  Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                                   (at level 20, dq custom dfrac at level 1, t at level 50,
                                    format "l  ↦[ t ] dq  v") : bi_scope.

  Ltac unseal := rewrite ?typed_pointsto_eq /typed_pointsto_def.

  Global Instance typed_pointsto_timeless l t q v: Timeless (l ↦[t]{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_fractional l t v: fractional.Fractional (λ q, l ↦[t]{#q} v)%I.
  Proof. unseal. apply _. Qed.

  (*
  Lemma typed_pointsto_singleton l q t v v0 :
    flatten_struct v = [v0] ->
    l ↦[t]{q} v ⊢@{_} l ↦{q} v0.
  Proof.
    intros Hv.
    unseal.
    rewrite Hv /=.
    by rewrite loc_add_0 right_id.
  Qed. *)

  Lemma typed_pointsto_ty q l v t :
    l ↦[t]{q} v ⊢@{_} ⌜has_go_type v t⌝.
  Proof. unseal. iIntros "[_ %] !%//". Qed.

  Local Lemma has_go_abstract_type_len {v t} :
    has_go_abstract_type v t ->
    length (flatten_struct v) = Z.to_nat (go_abstract_type_size t).
  Proof.
    unfold go_type_size.
    induction 1; simpl; auto.
    rewrite app_length. lia.
  Qed.

  Local Lemma has_go_type_len {v t} :
    has_go_type v t ->
    length (flatten_struct v) = Z.to_nat (go_type_size t).
  Proof.
    unfold go_type_size.
    induction 1; simpl; auto.
    rewrite app_length. lia.
  Qed.

  Lemma typed_pointsto_frac_valid l q t v :
    0 < go_type_size t →
    l ↦[t]{#q} v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    unseal.
    iIntros (?) "[Hvals %Hhas_go_type]".
    apply has_go_type_len in Hhas_go_type.
    destruct (flatten_struct v); simpl in *.
    - lia.
    - iDestruct "Hvals" as "[Hl _]".
      iDestruct (heap_pointsto_frac_valid with "Hl") as %Hq.
      auto.
  Qed.

  Local Lemma typed_pointsto_agree_flatten l t q1 v1 q2 v2 :
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

  Local Lemma flatten_struct_inj_helper v1 t1 :
    has_go_abstract_type v1 t1 ->
    (∀ t2 v2,
       has_go_abstract_type v2 t2 ->
       t1 = t2 →
       flatten_struct v1 = flatten_struct v2 ->
       v1 = v2).
  Proof.
    induction 1; last shelve; induction 1; simpl in *; try congruence.
    { intros ?. by injection 1 as ->. }
    { intros ?. by injection 1 as <-. }
    Unshelve.
    intros ??.
    destruct 1; try congruence.
    injection 1 as -> ->.
    specialize (IHhas_go_abstract_type1 _ _ H1_ eq_refl).
    specialize (IHhas_go_abstract_type2 _ _ H1_0 eq_refl).
    simpl. intros Hflat.
    apply app_inj_2 in Hflat as [].
    2:{ apply has_go_abstract_type_len in H0, H1_0. lia. }
    f_equal.
    + by apply IHhas_go_abstract_type1.
    + by apply IHhas_go_abstract_type2.
  Qed.

  Local Lemma flatten_struct_inj v1 v2 t :
    has_go_abstract_type v1 t ->
    has_go_abstract_type v2 t ->
    flatten_struct v1 = flatten_struct v2 ->
    v1 = v2.
  Proof. intros. by eapply flatten_struct_inj_helper. Qed.

  Lemma typed_pointsto_agree l t q1 v1 q2 v2 :
    l ↦[t]{q1} v1 -∗ l ↦[t]{q2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (typed_pointsto_ty with "Hl1") as %Hty1.
    iDestruct (typed_pointsto_ty with "Hl2") as %Hty2.
    pose proof (has_go_type_len Hty1).
    pose proof (has_go_type_len Hty2).
    iDestruct (typed_pointsto_agree_flatten with "Hl1 Hl2") as %Heq.
    { congruence. }
    iPureIntro.
    eapply flatten_struct_inj; eauto.
  Qed.

  Global Instance typed_pointsto_persistent l t v : Persistent (l ↦[t]□ v).
  Proof. rewrite typed_pointsto_eq. apply _. Qed.

  Lemma typed_pointsto_persist l dq t v:
    l ↦[t]{dq} v ==∗ l ↦[t]□ v.
  Proof.
    rewrite typed_pointsto_eq /typed_pointsto_def.
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
    rewrite typed_pointsto_eq /typed_pointsto_def /=.
    rewrite loc_add_0 right_id.
    iSplit.
    - iDestruct 1 as "[$ _]".
    - iDestruct 1 as "$". iPureIntro.
      unfold has_go_type. apply _.
  Qed.

  (* this is the core reasoning, not intended for external use *)
  Local Lemma wp_AllocAt t stk E v :
    has_go_type v t ->
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

  Lemma wp_ref_to t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref_to t v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_call.
    wp_apply (wp_AllocAt t); auto.
  Qed.

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    unfold has_go_type.
    destruct t; simpl; try apply _.
    FIXME:
  Qed.

  Lemma wp_ref_of_zero stk E t :
    {{{ True }}}
      ref (zero_val t) @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_AllocAt t); eauto.
  Qed.

  Lemma wp_LoadAt stk E q l t v :
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
      { erewrite has_go_type_flatten_length; eauto.
        setoid_rewrite ty_size_offset.
        rewrite Z.mul_1_r.
        iFrame. }
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite has_go_type_flatten_length by eauto.
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
    envs_lookup i Δ' = Some (false, typed_pointsto l q t v)%I →
    envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ???.
    rewrite -wp_bind. eapply bi.wand_apply; first by apply bi.wand_entails, wp_LoadAt.
    rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
    by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

  Lemma tac_wp_load_ty_persistent Δ s E i K l t v Φ :
    envs_lookup i Δ = Some (true, typed_pointsto l DfracDiscarded t v)%I →
    envs_entails Δ (WP fill K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? HΦ.
    rewrite -wp_bind. eapply bi.wand_apply; first by apply bi.wand_entails, wp_LoadAt.
    rewrite envs_lookup_split //; simpl.
    iIntros "[#Hp Henvs]".
    iSplitR; auto.
    iIntros "!> _".
    iApply HΦ.
    iApply ("Henvs" with "Hp").
  Qed.

  Lemma wp_store stk E l v v' :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /Store.
    wp_apply (wp_prepare_write with "Hl"); iIntros "[Hl Hl']".
    by wp_apply (wp_finish_store with "[$Hl $Hl']").
  Qed.

  Lemma wp_StoreAt stk E l t v0 v :
    has_go_type v t ->
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
      erewrite has_go_type_flatten_length by eauto.
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
      erewrite has_go_type_flatten_length by eauto.
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
    has_go_type v' t ->
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

Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                              (at level 20, dq custom dfrac at level 50, t at level 50,
                               format "l  ↦[ t ] dq  v") : bi_scope.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_ty _ _ _ _ _ K))
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [tc_solve
      |solve_pointsto ()
      |wp_finish] ) ||
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_ty_persistent _ _ _ _ K))
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [solve_pointsto ()
      |wp_finish] )
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
    [has_go_type
    |tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
