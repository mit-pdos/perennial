From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From New.golang.theory Require Import proofmode.
From iris.proofmode Require Import string_ident.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.theory Require Import typing assume list dynamic_typing.
(* re-export this theory since it provides ↦ notation *)
From New.golang.theory Require Export typed_pointsto.
From New.golang.defn Require Export mem.
From Perennial Require Export base.

Set Default Proof Using "Type".

Section goose_lang.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!IntoVal V}.

Context `{!IntoValTyped V t}.

Lemma wp_array_loc_add (l: loc) (i: w64) stk E :
  {{{ True }}}
    array_loc_add #t #l #i @ stk; E
  {{{ RET #(l +ₗ[t] (uint.Z i)); £1 ∗ ⌜go_type_size t < 2^64⌝ }}}.
Proof.
  rewrite array_loc_add_unseal.
  iIntros (Φ) "_ HΦ".
  wp_call_lc "Hlc".
  wp_apply wp_type_size.
  iIntros "[_ %]".
  wp_pures.
  wp_apply wp_assume_mul_no_overflow.
  iIntros "%".
  wp_pures.
  iDestruct ("HΦ" with "[$Hlc]") as "HΦ".
  { word. }
  iExactEq "HΦ".
  rewrite word.unsigned_mul_nowrap; [ | word ].
  repeat (f_equal; try word).
Qed.

Lemma wp_alloc (v : V) stk E :
  {{{ True }}}
    alloc (# v) @ stk; E
  {{{ l, RET #l; l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite alloc_unseal.
  wp_call.
  iApply (wp_alloc1_seq with "[//]"). iNext.
  iIntros (l) "Hl".
  rewrite to_val_unseal /= -to_val_unseal.
  iApply "HΦ".
  rewrite typed_pointsto_unseal /typed_pointsto_def /pointsto_vals.
  iFrame.
Qed.

Lemma wp_load_ty l (v: V) q stk E :
  {{{ ▷ l ↦{q} v }}}
    load_ty #t #l @ stk; E
  {{{ RET #v; l ↦{q} v }}}.
Proof using IntoValTyped0.
  rewrite load_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent (# v). clear dependent V.
  generalize dependent l.
  induction t using typing.go_type_ind;
    iIntros (l v Hty Φ) ">Hl HΦ";
    try solve [
        wp_call;
        inv Hty;
        rewrite to_val_unseal /= ?loc_add_0 ?right_id;
        iApply (wp_load with "[$Hl]");
        iFrame
      ].
  - (* arrayT *)
    wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty Hbound.
    wp_apply wp_type_size. iIntros "[_ %Hsz]". wp_pures.
    iInduction n as [|n] "IH" forall (l v Hbound Hty Φ).
    + rewrite bool_decide_eq_true_2; [ wp_pures | word ].
      inv Hty.
      assert (a = []) by (destruct a; naive_solver); subst; simpl.
      rewrite to_val_unseal /=.
      iApply "HΦ". iFrame.
    + rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      apply has_go_type_array_S_inv in Hty as (v0 & v' & -> & Hty0 & Hty); [ | word ].
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply (IHg with "[$Hl1]").
      { auto. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply ("IH" $! _ v' with "[] [] [Hl2]").
      { word. }
      { iPureIntro. auto. }
      { rewrite -/flatten_struct. erewrite has_go_type_len by eauto.
        replace (uint.Z (W64 (go_type_size g))) with (Z.of_nat (go_type_size g)) by word.
        setoid_rewrite loc_add_assoc.
        setoid_rewrite Nat2Z.inj_add.
        iFrame "Hl2". }
      iIntros "Hl2".
      wp_pures.
      iApply "HΦ".
      rewrite big_sepL_app.
      rewrite -/flatten_struct.
      iFrame "Hl1".
      erewrite has_go_type_len by eauto.
      replace (uint.Z (W64 (go_type_size g))) with (Z.of_nat (go_type_size g)) by word.
      setoid_rewrite loc_add_assoc.
      setoid_rewrite Nat2Z.inj_add.
      iFrame "Hl2".
  - (* interfaceT *)
    inv Hty.
    wp_call.
    destruct i;
      rewrite to_val_unseal /= ?loc_add_0 ?right_id;
      iApply (wp_load with "[$Hl]");
      iFrame.
  - (* structT *)
    wp_call.
    rewrite -load_ty_unseal.
    iInduction decls as [|[f ft] decls] forall (l Φ v Hty).
    + wp_pures.
      inv Hty.
      rewrite struct.val_aux_unseal /=.
      rewrite to_val_unseal /=.
      by iApply "HΦ".
    + (* make the goal readable *)
      match goal with
      | |- context[Esnoc _ (INamed "IHdecls") ?P] =>
          set (IHdeclsP := P)
      end.
      wp_pures.
      rewrite [in # (f :: ft)%struct]to_val_unseal /=.
      wp_pures.
      pose proof Hty as Hty'.
      inv Hty.
      apply has_go_type_struct_pair_inv in Hty' as [Hty1 Hty2].
      rewrite struct.val_aux_unseal /=.
      iDestruct (big_sepL_app with "Hl") as "[Hv Hl]".
      rewrite load_ty_unseal.
      wp_apply (Hfields with "[$Hv]").
      { naive_solver. }
      { naive_solver. }
      iIntros "Hv".
      wp_pures.
      wp_apply wp_type_size.
      iIntros "[_ %]".
      wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      rewrite !Z.mul_1_l.
      replace (uint.Z (W64 (go_type_size ft))) with
        (Z.of_nat (go_type_size ft)) by word.
      rewrite -load_ty_unseal.
      iApply ("IHdecls" with "[] [] [Hl]").
      { iPureIntro.
        naive_solver. }
      {
        iPureIntro.
        eauto.
      }
      {
        rewrite struct.val_aux_unseal.
        erewrite -> has_go_type_len by eauto.
        setoid_rewrite Nat2Z.inj_add.
        setoid_rewrite loc_add_assoc.
        iFrame "Hl".
      }
      iIntros "Hl".
      wp_pures.
      rewrite struct.val_aux_unseal.
      iApply "HΦ".
      iApply big_sepL_app.
      iFrame "Hv".
      erewrite -> has_go_type_len by eauto.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite loc_add_assoc.
      iFrame "Hl".
Qed.

Lemma wp_store_ty l (v0 v: V) stk E :
  {{{ ▷l ↦ v0 }}}
    store_ty #t #l #v @ stk; E
  {{{ RET #(); l ↦ v }}}.
Proof using IntoValTyped0.
  rewrite store_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  pose proof (to_val_has_go_type v0) as Hty0.
  generalize dependent (# v). generalize dependent (# v0). clear dependent V.
  generalize dependent l.
  induction t using typing.go_type_ind;
    iIntros (l v0 Hty0 v Hty Φ) ">Hl HΦ";
    try solve [
        wp_call;
        inv Hty0;
        inv Hty;
        rewrite to_val_unseal /= ?loc_add_0 ?right_id;
        iApply (wp_store with "[$Hl]");
        iFrame
      ].
  - (* arrayT *)
    wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty0 Hty Hbound.
    wp_apply wp_type_size. iIntros "[_ %Hsz]". wp_pures.
    iInduction n as [|n] "IH" forall (l v0 v Hbound Hty0 Hty Φ).
    + rewrite bool_decide_eq_true_2; [ wp_pures | word ].
      inv Hty.
      assert (a = []) by (destruct a; naive_solver); subst; simpl.
      rewrite to_val_unseal /=.
      iApply "HΦ". done.
    + rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      apply has_go_type_array_S_inv in Hty as (v1 & v1' & -> & Hty1 & Hty1'); [ | word ].
      apply has_go_type_array_S_inv in Hty0 as (v & v0' & -> & Hty0 & Hty0'); [ | word ].
      rename v into v0.
      wp_pures.
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply (IHg with "[$Hl1]").
      { auto. }
      { auto. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply ("IH" $! _ v0' v1' with "[] [] [] [Hl2]").
      { word. }
      { iPureIntro. eauto. }
      { iPureIntro. eauto. }
      { rewrite -/flatten_struct. erewrite has_go_type_len by eauto.
        replace (uint.Z (W64 (go_type_size g))) with (Z.of_nat (go_type_size g)) by word.
        setoid_rewrite loc_add_assoc.
        setoid_rewrite Nat2Z.inj_add.
        iFrame "Hl2". }
      iIntros "Hl2".
      wp_pures.
      iApply "HΦ".
      rewrite big_sepL_app.
      rewrite -/flatten_struct.
      iFrame "Hl1".
      erewrite has_go_type_len by eauto.
      replace (uint.Z (W64 (go_type_size g))) with (Z.of_nat (go_type_size g)) by word.
      setoid_rewrite loc_add_assoc.
      setoid_rewrite Nat2Z.inj_add.
      iFrame "Hl2".
  - (* interfaceT *)
    inv Hty.
    inv Hty0.
    wp_call.
    destruct i, i0;
      rewrite to_val_unseal /= ?loc_add_0 ?right_id;
      iApply (wp_store with "[$Hl]");
      iFrame.
  - (* structT *)
    wp_call.
    rewrite -store_ty_unseal.
    iInduction decls as [|[f ft] decls] forall (l Φ v Hty v0 Hty0).
    + wp_pures.
      inv Hty.
      rewrite struct.val_aux_unseal /=.
      rewrite to_val_unseal /=.
      by iApply "HΦ".
    + (* make the goal readable *)
      match goal with
      | |- context[Esnoc _ (INamed "IHdecls") ?P] =>
          set (IHdeclsP := P)
      end.
      wp_pures.
      rewrite [in # (f :: ft)%struct]to_val_unseal /=.
      wp_pures.
      pose proof Hty as Hty'.
      inv Hty.
      apply has_go_type_struct_pair_inv in Hty' as [Hty1 Hty2].
      pose proof Hty0 as Hty0'.
      inv Hty0.
      apply has_go_type_struct_pair_inv in Hty0' as [Hty0_1 Hty0_2].
      rewrite struct.val_aux_unseal /=.
      iDestruct (big_sepL_app with "Hl") as "[Hv Hl]".
      wp_pures.
      rewrite store_ty_unseal.
      wp_apply (Hfields with "[$Hv]").
      { naive_solver. }
      { auto. }
      { auto. }
      iIntros "Hv".
      wp_pures.
      wp_apply wp_type_size.
      iIntros "[_ %]".
      wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      rewrite !Z.mul_1_l.
      replace (uint.Z (W64 (go_type_size ft))) with
        (Z.of_nat (go_type_size ft)) by word.
      rewrite -store_ty_unseal.
      iApply ("IHdecls" with "[] [] [] [Hl]").
      { iPureIntro.
        naive_solver. }
      {
        iPureIntro.
        rewrite -/(struct.val_aux_def (structT decls) _).
        rewrite -struct.val_aux_unseal.
        apply has_go_type_struct; naive_solver.
      }
      {
        eauto.
      }
      {
        rewrite struct.val_aux_unseal.
        erewrite -> has_go_type_len by eauto.
        setoid_rewrite Nat2Z.inj_add.
        setoid_rewrite loc_add_assoc.
        iFrame "Hl".
      }
      iIntros "Hl".
      wp_pures.
      iApply "HΦ".
      iApply big_sepL_app.
      iFrame "Hv".
      erewrite -> has_go_type_len by eauto.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite loc_add_assoc.
      iFrame "Hl".
Qed.

Definition is_primitive_type (t : go_type) : Prop :=
  match t with
  | structT d => False
  | arrayT n t => False
  | funcT => False
  | sliceT => False
  | interfaceT => False
  | _ => True
  end.

Lemma wp_typed_cmpxchg_fail l dq (v' v1 v2: V) s E :
  is_primitive_type t →
  #v' ≠ #v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val # l) #v1 #v2 @ s; E
  {{{ RET (#v', #false); l ↦{dq} v' }}}.
Proof using Type*.
  pose proof (to_val_has_go_type v') as Hty_old.
  pose proof (to_val_has_go_type v1) as Hty.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  generalize dependent (to_val v1). generalize dependent (to_val v'). generalize dependent (to_val v2).
  intros.
  clear dependent V.
  rewrite to_val_unseal.
  iIntros "Hl HΦ".
  destruct t; try by exfalso.
  all: inversion Hty_old; subst; inversion Hty; subst;
    simpl; rewrite to_val_unseal /= in H0 |- *;
    rewrite loc_add_0 right_id;
    iApply (wp_cmpxchg_fail with "[$]"); first done; first (by econstructor);
    iIntros; iApply "HΦ"; iFrame; done.
Qed.

Lemma wp_typed_cmpxchg_suc l (v' v1 v2: V) s E :
  is_primitive_type t →
  #v' = #v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg #l #v1 #v2 @ s; E
  {{{ RET (#v', #true); l ↦ v2 }}}.
Proof using Type*.
  intros Hprim Heq.
  pose proof (to_val_has_go_type v') as Hty_old.
  pose proof (to_val_has_go_type v2) as Hty.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  generalize dependent (#v1). generalize dependent (#v'). generalize dependent (#v2).
  clear dependent V.
  intros.
  iIntros "Hl HΦ".
  destruct t; try by exfalso.
  all: inversion Hty_old; subst;
    inversion Hty; subst;
    simpl; rewrite to_val_unseal /= loc_add_0 !right_id;
    iApply (wp_cmpxchg_suc with "[$Hl]"); first done; first (by econstructor);
    iIntros; iApply "HΦ"; iFrame; done.
Qed.

Lemma wp_typed_Load (l : loc) (v : V) dq s E :
  is_primitive_type t →
  {{{ l ↦{dq} v }}}
    ! #l @ s ; E
  {{{ RET #v; l ↦{dq} v }}}.
Proof using Type*.
  intros Hprim.
  pose proof (to_val_has_go_type v) as Hty.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  generalize dependent (#v).
  clear dependent V.
  intros.
  iIntros "Hl HΦ".
  destruct t; try by exfalso.
  all: inversion Hty; subst;
    inversion Hty; subst;
    simpl; rewrite to_val_unseal /= loc_add_0 !right_id;
    iApply (wp_load with "[$Hl]"); iFrame.
Qed.

Lemma wp_typed_AtomicStore s E (l : loc) (v v' : V) :
  is_primitive_type t →
  {{{ l ↦ v }}}
    AtomicStore #l #v' @ s ; E
  {{{ RET #(); l ↦ v' }}}.
Proof using Type*.
  intros Hprim.
  pose proof (to_val_has_go_type v) as Hty_old.
  pose proof (to_val_has_go_type v') as Hty.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  generalize dependent (#v). generalize dependent (#v').
  clear dependent V.
  intros.
  iIntros "Hl HΦ".
  destruct t; try by exfalso.
  all: inversion Hty; subst;
    inversion Hty_old; inversion Hty; subst;
    simpl; rewrite to_val_unseal /= loc_add_0 !right_id;
    iApply (wp_atomic_store with "[$Hl]"); iFrame.
Qed.

End goose_lang.

Section tac_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Lemma tac_wp_load_ty {V t} `{!IntoVal V} `{!IntoValTyped V t}
    K (l : loc) (v : V) Δ s E i dq Φ is_pers
    `{!PointsToAccess l v dq P P'} :
    envs_lookup i Δ = Some (is_pers, P)%I →
    envs_entails Δ (WP (fill K (Val #v)) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (load_ty #t #l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ? HΦ.
    rewrite envs_lookup_split //.
    iIntros "[H Henv]".
    destruct is_pers; simpl.
    - iDestruct "H" as "#H".
      iDestruct (points_to_acc with "H") as "[H' _]".
      wp_apply (@wp_load_ty with "[$]").
      iIntros "?".
      iApply HΦ. iApply "Henv". iFrame "#".
    - iDestruct (points_to_acc with "H") as "[H Hclose]".
      wp_apply (@wp_load_ty with "[$]").
      iIntros "?".
      iApply HΦ. iApply "Henv".
      iSpecialize ("Hclose" with "[$]").
      rewrite points_to_update_eq. iFrame.
  Qed.

  Lemma tac_wp_store_ty {V t} `{!IntoVal V} `{!IntoValTyped V t}
    K (l : loc) (v v' : V) Δ Δ' s E i Φ
    `{!PointsToAccess l v (DfracOwn 1) P P'} :
    envs_lookup i Δ = Some (false, P)%I →
    envs_simple_replace i false (Esnoc Enil i (P' v')) Δ = Some Δ' →
    envs_entails Δ' (WP fill K (Val #()) @ s ; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (store_ty #t #l (Val #v'))) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ?? HΦ.
    rewrite envs_simple_replace_sound // /=.
    iIntros "[H Henv]".
    iDestruct (points_to_acc with "H") as "[H Hclose]".
    wp_apply (@wp_store_ty with "[$]").
    iIntros "H". iSpecialize ("Hclose" with "[$]").
    iApply HΦ.
    iApply "Henv". iFrame.
  Qed.

  Lemma tac_wp_alloc
    `{!IntoVal V}
    K Δ stk E (v : V) Φ :
    (∀ l, envs_entails Δ (l ↦ v -∗ WP (fill K (Val #l)) @ stk; E {{ Φ }})) →
    envs_entails Δ (WP fill K (alloc #v) @ stk; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hwp.
    iIntros "Henv".
    wp_apply wp_alloc. iIntros.
    by iApply (Hwp with "[$]").
  Qed.

  Global Instance points_to_access_trivial {V} l (v : V) {t} `{!IntoVal V} `{!IntoValTyped V t} dq
    : PointsToAccess l v dq (l ↦{dq} v)%I (λ v', l ↦{dq} v')%I.
  Proof. constructor; [eauto with iFrame|done]. Qed.

End tac_lemmas.

Ltac2 wp_load_visit e k :=
  Control.once_plus (fun () => Std.unify e '(load_ty _ (Val _)))
         (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_load_ty $k) > [tc_solve_many ()| ltac1:(iAssumptionCore) | ectx_simpl ()])
    (fun _ => Control.backtrack_tactic_failure "wp_load: could not find a points-to in context covering the address")
.

Ltac2 wp_load () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_load_visit)
                                                        "wp_load: could not find load_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_load: not a wp"
  end.

Ltac2 wp_store_visit e k :=
  Control.once_plus (fun () => (Std.unify e '(store_ty _ _ (Val _))))
         (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_store_ty $k) > [tc_solve_many ()| ltac1:(iAssumptionCore)
                                           |ltac1:(pm_reflexivity) | ectx_simpl () ])
    (fun _ => Control.backtrack_tactic_failure "wp_store: could not find a points-to in context covering the address")
.

Ltac2 wp_store () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_store_visit)
                                                        "wp_store: could not find store_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_store: not a wp"
  end.

Ltac2 wp_alloc_visit e k :=
  Control.once_plus (fun () => Std.unify e '(alloc (Val _)))
    (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_alloc $k); ectx_simpl ())
    (fun _ => Control.backtrack_tactic_failure "wp_alloc: failed to apply tac_wp_alloc")
.

Ltac2 wp_alloc () :=
  ltac1:(rewrite <- ?default_val_eq_zero_val);
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_alloc_visit)
                                                        "wp_alloc: could not find ref_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_alloc: not a wp"
  end.

Ltac2 wp_alloc_auto_visit e k :=
  lazy_match! e with
  (* Manually writing out [let: ?var_name := (alloc (Val _)) in ?e1] to get
     pattern matching to work. *)
  | (App (Rec BAnon (BNamed ?var_name) ?e1) (App (Val alloc) (Val _))) =>
      let let_expr1 := '(Rec BAnon (BNamed $var_name) $e1) in
      let ptr_name := Std.eval_vm None constr:($var_name +:+ "_ptr") in
      let k := constr:(@AppRCtx _ $let_expr1 :: $k) in
      Control.once_plus (fun _ => eapply (tac_wp_alloc $k); ectx_simpl ())
        (fun _ => Control.backtrack_tactic_failure "wp_alloc_auto: failed to apply tac_wp_alloc");
      let i :=
        orelse (fun () => Option.get_bt (Ident.of_string (StringToIdent.coq_string_to_string ptr_name)))
          (fun _ => Control.backtrack_tactic_failure "wp_alloc_auto: could not convert to ident") in
      Std.intros false [Std.IntroNaming (Std.IntroIdentifier i)];
      ltac1:(hyp_name |- iIntros hyp_name) (Ltac1.of_constr var_name)
  | _ => Control.zero Walk_expr_more
  end.

Ltac2 wp_alloc_auto () :=
  (* XXX: the zero_val pure expression appears after the PureWp reduction of
  type.zero_val, but there's currently no way to put that simplification after
  that specific reduction *)
  ltac1:(rewrite <- ?default_val_eq_zero_val);
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_alloc_auto_visit)
                                                        "wp_alloc_auto: could not find ref_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_alloc_auto: not a wp"
  end.

Tactic Notation "wp_alloc_auto" :=
  ltac2:(Control.enter wp_alloc_auto).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  ltac2:(Control.enter wp_alloc);
  intros l;
  iIntros H.

Tactic Notation "wp_load" := ltac2:(Control.enter wp_load).
Tactic Notation "wp_store" := ltac2:(Control.enter wp_store).
