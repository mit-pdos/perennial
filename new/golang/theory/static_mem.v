From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From iris.bi.lib Require Import fractional.
From Perennial.program_logic Require Import weakestpre.
From New.golang.defn Require Export static_mem.
From New.golang.theory Require Import proofmode list typing typed_pointsto.
From iris.proofmode Require Import string_ident.
Require Import Coq.Program.Equality.


(** High-level memory. Replaced with memory based on dynamic types in mem.v.
This file is left only as a demo. *)

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Context `{!IntoVal V}.
  Context `{!IntoValTyped V t}.
  Implicit Type v : V.
  Lemma wp_ref_ty stk E (v : V) :
    {{{ True }}}
      ref_ty t (# v) @ stk; E
    {{{ l, RET #l; l ↦ v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite ref_ty_unseal.
    wp_call.
    iApply (wp_alloc1_seq with "[//]"). iNext.
    iIntros (l) "Hl".
    rewrite to_val_unseal /= -to_val_unseal.
    iApply "HΦ".
    rewrite typed_pointsto_unseal.
    iFrame.
  Qed.

  Lemma wp_load_ty stk E q l v :
    {{{ ▷ l ↦{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET #v; l ↦{q} v }}}.
  Proof using IntoValTyped0.
    iIntros (Φ) ">Hl HΦ".
    rewrite typed_pointsto_unseal /typed_pointsto_def.
    pose proof (to_val_has_go_type v) as Hty.
    generalize dependent (# v). clear dependent V.
    intros v Hty.
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, heap_pointsto (l +ₗ j) q vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ". iFrame. }
    rewrite load_ty_unseal.
    rename l into l'.
    iInduction Hty as [] "IH" forall (l' Φ) "HΦ".
    all: try destruct i.
    all: rewrite ?to_val_unseal /= /= ?loc_add_0 ?right_id; wp_pures.
    all: try (iApply (wp_load with "[$]"); done).
    - (* case arrayT *)
      rewrite -Hlen.
      generalize dependent (uint.nat n); intros n' ?.
      subst n'.
      iInduction a as [|v a'] "IH2" forall (l' Φ).
      { simpl.
        wp_pures.
        rewrite to_val_unseal. iApply "HΦ". by iFrame. }
      wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      fold flatten_struct.
      simpl. wp_pures.
      simpl.
      wp_apply ("IH" with "[] Hf").
      { iPureIntro. by left. }
      iIntros "Hf".
      wp_pures.
      replace (LitV (LitLoc l')) with (# l').
      2:{ by rewrite to_val_unseal. }
      wp_pures.
      rewrite to_val_unseal /=.
      wp_apply ("IH2" with "[] [] [Hl]").
      { iPureIntro. intros. apply Helems. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [$] [$]").
        iPureIntro. by right. }
      {
        erewrite has_go_type_len.
        2:{ eapply Helems. by left. }
        rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
        iFrame.
      }
      iIntros "Hl".
      wp_pures.
      iApply "HΦ".
      iFrame.
      fold flatten_struct.
      erewrite has_go_type_len.
      2:{ eapply Helems. by left. }
      rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      by iFrame.
    - (* case structT *)
      rewrite struct.val_aux_unseal.
      iInduction d as [|] "IH2" forall (l' Φ).
      { wp_pures. iApply "HΦ". by iFrame. }
      destruct a.
      wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      fold flatten_struct.
      wp_apply ("IH" with "[] Hf").
      { iPureIntro. by left. }
      iIntros "Hf".
      replace (LitV (LitLoc l')) with (# l').
      2:{ by rewrite to_val_unseal. }
      wp_pures.
      simpl. wp_bind.
      rewrite [in (to_val (l' +ₗ _))]to_val_unseal.
      wp_apply ("IH2" with "[] [] [Hl]").
      { iPureIntro. intros. apply Hfields. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [$] [$]").
        iPureIntro. by right. }
      {
        erewrite has_go_type_len.
        2:{ eapply Hfields. by left. }
        rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
        iFrame.
      }
      iIntros "Hl".
      wp_pures.
      iApply "HΦ".
      iFrame.
      erewrite has_go_type_len.
      2:{ eapply Hfields. by left. }
      rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      by iFrame.
  Qed.

  Lemma wp_store_ty stk E l v v' :
    {{{ ▷ l ↦ v }}}
      store_ty t #l #v' @ stk; E
    {{{ RET #(); l ↦ v' }}}.
  Proof using IntoValTyped0.
    iIntros (Φ) ">Hl HΦ".
    rewrite typed_pointsto_unseal /typed_pointsto_def.
    pose proof (to_val_has_go_type v) as Hty_old.
    pose proof (to_val_has_go_type v') as Hty.
    generalize dependent #v. generalize dependent #v'.
    clear dependent V. intros v' Hty v Hty_old.
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v', heap_pointsto (l +ₗ j) (DfracOwn 1) vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ". iFrame. }
    rename l into l'.
    rewrite store_ty_unseal.
    iInduction Hty_old as [] "IH" forall (v' Hty l' Φ) "HΦ".
    all: inversion_clear Hty; subst;
      try destruct i, i0; rewrite ?to_val_unseal /= ?loc_add_0 ?right_id; wp_pures.
    all: try (wp_apply (wp_store with "[$]"); iIntros "H"; iApply "HΦ"; iFrame).
    - (* array *)
      rename a0 into a'.
      rewrite -Hlen.
      generalize dependent (uint.nat n); intros n' ??.
      subst n'.
      iInduction a as [|v a] "IH2" forall (l' a' Hlen0 Helems0).
      { simpl. wp_pures. rewrite ?to_val_unseal. iApply "HΦ".
        dependent destruction a'; done. }
      simpl. wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      fold flatten_struct.
      erewrite has_go_type_len.
      2:{ eapply Helems. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      destruct a' as [|v'' a']; [ done | ].
      simpl.
      wp_pures.
      wp_apply ("IH" with "[] [] [$Hf]").
      { iPureIntro. simpl. by left. }
      { iPureIntro. apply Helems0. by left. }
      iIntros "Hf".
      replace (LitV l') with (#l').
      2:{ rewrite to_val_unseal //. }
      wp_pures.
      rewrite [in (to_val (l' +ₗ _))]to_val_unseal.
      wp_apply ("IH2" with "[] [] [] [] [Hl]").
      { iPureIntro. intros. apply Helems. by right. }
      { simpl in *; iPureIntro; lia. }
      { iPureIntro. intros. apply Helems0. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [//] [$] [$]"). iPureIntro. by right. }
      { rewrite ?right_id. iFrame. }
      iIntros "Hl".
      iApply "HΦ".
      iFrame.
      fold flatten_struct.
      erewrite has_go_type_len.
      2:{ eapply Helems0. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      rewrite ?right_id. iFrame.
    - (* struct *)
      rewrite struct.val_aux_unseal.
      unfold struct.val_aux_def.
      iInduction d as [|] "IH2" forall (l').
      { wp_pures. rewrite to_val_unseal /=. iApply "HΦ". done. }
      destruct a.
      wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      fold flatten_struct.
      erewrite has_go_type_len.
      2:{ eapply Hfields. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      wp_apply ("IH" with "[] [] [$Hf]").
      { iPureIntro. simpl. by left. }
      { iPureIntro. apply Hfields0. by left. }
      iIntros "Hf".
      replace (LitV l') with (#l').
      2:{ rewrite to_val_unseal //. }
      wp_pures.
      rewrite [in (to_val (l' +ₗ _))]to_val_unseal.
      wp_apply ("IH2" with "[] [] [] [Hl]").
      { iPureIntro. intros. apply Hfields. by right. }
      { iPureIntro. intros. apply Hfields0. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [//] [$] [$]"). iPureIntro. by right. }
      { rewrite ?right_id. iFrame. }
      iIntros "Hl".
      iApply "HΦ".
      iFrame.
      fold flatten_struct.
      erewrite has_go_type_len.
      2:{ eapply Hfields0. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      rewrite ?right_id. iFrame.
  Qed.

End goose_lang.

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                              (at level 20, dq custom dfrac at level 50,
                               format "l  ↦ dq  v") : bi_scope.

Section tac_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Lemma tac_wp_load_ty {V t} `{!IntoVal V} `{!IntoValTyped V t}
    K (l : loc) (v : V) Δ s E i dq Φ is_pers
    `{!PointsToAccess l v dq P P'} :
    envs_lookup i Δ = Some (is_pers, P)%I →
    envs_entails Δ (WP (fill K (Val #v)) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (load_ty t #l)) @ s; E {{ Φ }}).
  Proof using Type*.
    rewrite envs_entails_unseal => ? HΦ.
    rewrite envs_lookup_split //.
    iIntros "[H Henv]".
    destruct is_pers; simpl.
    - iDestruct "H" as "#H".
      iDestruct (points_to_acc with "H") as "[H' _]".
      unshelve wp_apply (wp_load_ty with "[$]"); first apply _.
      iIntros "?".
      iApply HΦ. iApply "Henv". iFrame "#".
    - iDestruct (points_to_acc with "H") as "[H Hclose]".
      unshelve wp_apply (wp_load_ty with "[$]"); first apply _.
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
    envs_entails Δ (WP (fill K (store_ty t #l (Val #v'))) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ?? HΦ.
    rewrite envs_simple_replace_sound // /=.
    iIntros "[H Henv]".
    iDestruct (points_to_acc with "H") as "[H Hclose]".
    unshelve wp_apply (wp_store_ty with "[$]"); first tc_solve.
    iIntros "H". iSpecialize ("Hclose" with "[$]").
    iApply HΦ.
    iApply "Henv". iFrame.
  Qed.

  Lemma tac_wp_ref_ty
    `{!IntoVal V} `{!IntoValTyped V t}
    K Δ stk E (v : V) Φ :
    (∀ l, envs_entails Δ (l ↦ v -∗ WP (fill K (Val #l)) @ stk; E {{ Φ }})) →
    envs_entails Δ (WP fill K (ref_ty t #v) @ stk; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hwp.
    iIntros "Henv".
    wp_apply wp_ref_ty. iIntros.
    by iApply (Hwp with "[$]").
  Qed.

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
  Control.once_plus (fun () => Std.unify e '(ref_ty _ (Val _)))
    (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_ref_ty $k); ectx_simpl ())
    (fun _ => Control.backtrack_tactic_failure "wp_alloc: failed to apply tac_wp_ref_ty")
.

Ltac2 wp_alloc () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_alloc_visit)
                                                        "wp_alloc: could not find ref_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_alloc: not a wp"
  end.

Ltac2 wp_alloc_auto_visit e k :=
  lazy_match! e with
  (* Manually writing out [let: ?var_name := (ref_ty _ (Val _)) in ?e1] to get
     pattern matching to work. *)
  | (App (Rec BAnon (BNamed ?var_name) ?e1) (App (Val (ref_ty _)) (Val _))) =>
      let let_expr1 := '(Rec BAnon (BNamed $var_name) $e1) in
      let ptr_name := Std.eval_vm None constr:($var_name +:+ "_ptr") in
      let k := constr:(@AppRCtx _ $let_expr1 :: $k) in
      Control.once_plus (fun _ => eapply (tac_wp_ref_ty $k); ectx_simpl ())
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
