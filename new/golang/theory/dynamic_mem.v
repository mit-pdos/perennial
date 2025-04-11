From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From New.golang.theory Require Import proofmode.
From iris.proofmode Require Import string_ident.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.theory Require Import typing assume list mem dynamic_typing.
From New.golang.defn Require Export dynamic_mem.

Set Default Proof Using "Type".

Section goose_lang.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!IntoVal V}.

Context `{!IntoValTyped V t}.

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
Proof.
  (*
  iIntros (Φ) ">Hl HΦ".
  rewrite type.load_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent (# v). clear dependent V.
  intros v Hty.
  rename l into l'.
  iInduction Hty as [] "IH" forall (l' Φ) "HΦ".
  all: try destruct i.
  all: rewrite ?[in flatten_struct _]to_val_unseal /= /= ?loc_add_0 ?right_id; wp_pures.
  all:
    try solve [ wp_call; rewrite !to_val_unseal /=;
                           iApply (wp_load with "[$]");
                iIntros "!> H"; rewrite ?to_val_unseal /=; iApply "HΦ"; done
      ].

  {
    wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty Hbound.
    clear Hty.
    iInduction n as [|n] "IHn" forall (l' a Φ).
    - admit.
    - rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      destruct a as [|t' a']; simpl in *; [ word | ].
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply ("IH" with "[] [$Hl1]").
      { naive_solver. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply "IHn".
      iApply ("IH" $! _ _ (foldr PairV (#()) a') with "[] [] [Hl2]").
      { iPureIntro. apply has_go_type_array.
        - word.
        - naive_solver. }
      {
        iPureIntro. rewrite app_length in Hlen.
        apply has_go_type_len in H.
  }
   *)

  rewrite load_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent (# v). clear dependent V.
  generalize dependent l.
  induction t using go_type_ind;
    iIntros (l v Hty Φ) ">Hl HΦ";
    try solve [
        wp_call;
        inv Hty;
        rewrite to_val_unseal /= ?loc_add_0 ?right_id;
        iApply (wp_load with "[$Hl]");
        iFrame
      ].
  - wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty Hbound.
    wp_apply wp_type_size. iIntros "[_ %Hsz]". wp_pures.
    iInduction n as [|n] "IH" forall (l v Hty Φ).
    + rewrite bool_decide_eq_true_2; [ wp_pures | word ].
      inv Hty.
      assert (a = []) by (destruct a; naive_solver); subst; simpl.
      rewrite to_val_unseal /=.
      iApply "HΦ". iFrame.
    + rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      assert (length (flatten_struct v) = (S n * go_type_size g)%nat) as Hlen.
      {
        apply has_go_type_len in Hty.
        rewrite Hty.
        rewrite go_type_size_unseal /=.
        rewrite -go_type_size_unseal.
        replace (uint.nat (W64 (S n))) with (S n) by word.
        reflexivity.
      }
      pose proof Hty as Hty'.
      inv Hty.
      destruct a as [|t' a']; simpl in *; [ word | ].
      rewrite length_app in Hlen.
      assert (has_go_type t' g) as Ht' by naive_solver.
      pose proof Ht' as Hlen'. apply has_go_type_len in Hlen'.
      rewrite Hlen' in Hlen.
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply (IHg with "[$Hl1]").
      { auto. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply ("IH" $! _ _ (foldr PairV (#()) a') with "[] [Hl2]").
      { iPureIntro. apply has_go_type_array.
        - word.
        - naive_solver. }
      { rewrite Hlen'.
        iApply (big_sepL_impl with "Hl2").
        iIntros "!>" (???) "H".
        iExactEq "H".
        rewrite loc_add_assoc.
        repeat (f_equal; try word). }
      iIntros "Hl2".
      wp_pures.
      iApply "HΦ".
      rewrite big_sepL_app.
      rewrite Hlen'.
      iFrame "Hl1".
      iApply (big_sepL_impl with "Hl2").
      iIntros "!>" (???) "H".
      iExactEq "H".
      rewrite loc_add_assoc.
      repeat (f_equal; try word).
  - inv Hty.
    wp_call.
    destruct i;
      rewrite to_val_unseal /= ?loc_add_0 ?right_id;
      iApply (wp_load with "[$Hl]");
      iFrame.
  - (* structT *)
    wp_call.
    admit.
Admitted.

Lemma wp_store_ty l (v0 v: V) stk E :
  {{{ ▷l ↦ v0 }}}
    store_ty #t #l #v @ stk; E
  {{{ RET #(); l ↦ v }}}.
Proof.
Admitted.

End goose_lang.

Section tac_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Lemma tac_wp_load_ty {V t} `{!IntoVal V} `{!IntoValTyped V t}
    K (l : loc) (v : V) Δ s E i dq Φ is_pers
    `{!PointsToAccess l v dq P P'} :
    envs_lookup i Δ = Some (is_pers, P)%I →
    envs_entails Δ (WP (fill K (Val #v)) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (load_ty #t #l)) @ s; E {{ Φ }}).
  Proof using Type*.
    rewrite envs_entails_unseal => ? HΦ.
    rewrite envs_lookup_split //.
    iIntros "[H Henv]".
    destruct is_pers; simpl.
    - iDestruct "H" as "#H".
      iDestruct (points_to_acc with "H") as "[H' _]".
      wp_apply (wp_load_ty with "[$]").
      iIntros "?".
      iApply HΦ. iApply "Henv". iFrame "#".
    - iDestruct (points_to_acc with "H") as "[H Hclose]".
      wp_apply (wp_load_ty with "[$]").
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
    wp_apply (wp_store_ty with "[$]").
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
        (fun _ => Control.backtrack_tactic_failure "wp_alloc_auto: failed to apply tac_wp_ref_ty");
      let i :=
        orelse (fun () => Option.get_bt (Ident.of_string (StringToIdent.coq_string_to_string ptr_name)))
          (fun _ => Control.backtrack_tactic_failure "wp_alloc_auto: could not convert to ident") in
      Std.intros false [Std.IntroNaming (Std.IntroIdentifier i)];
      ltac1:(hyp_name |- iIntros hyp_name) (Ltac1.of_constr var_name)
  | _ => Control.zero Walk_expr_more
  end.

Ltac2 wp_alloc_auto () :=
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
