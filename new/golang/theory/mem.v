From iris.proofmode Require Import coq_tactics reduction environments.
From iris.bi.lib Require Import fractional.
From Perennial.program_logic Require Import weakestpre.
From New.golang.theory Require Import predeclared.
From iris.proofmode Require Import string_ident.
Require Import Coq.Program.Equality.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Set Default Proof Using "Type".

Section goose_lang.

  Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
    {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

  Class AtomicWps V `{!TypedPointsto (Σ:=Σ) V} `{!ZeroVal V} :=
    {
      wp_cmpxchg_fail l (v' v1 v2 : V) dq stk E :
      (v' ≠ v1 →
       {{{ ▷ l ↦{dq} v' }}} CmpXchg #l #v1 #v2 @ stk; E {{{ RET (#v', #false); l ↦{dq} v' }}});

      wp_cmpxchg_suc l (v' v1 v2 : V) stk E :
        (v' = v1 →
        {{{ ▷ l ↦ v' }}} CmpXchg #l #v1 #v2 @ stk; E {{{ RET (#v', #true); l ↦ v2 }}});

      wp_atomic_load stk E l dq (v : V) :
        ({{{ ▷ l ↦{dq} v }}} ! #l @ stk ; E {{{ RET #v; l ↦{dq} v }}});

      wp_atomic_swap s E (l : loc) (v v' : V) :
      ({{{ l ↦ v }}} AtomicSwap #l #v' @ s ; E {{{ RET #v; l ↦ v' }}});
    }.
  Global Hint Mode AtomicWps + - - : typeclass_instances.

  Ltac solve_cmpxchg_fail :=
    iIntros "* %Hne % Hl HΦ"; rewrite typed_pointsto_unseal /= !go.into_val_unfold;
      iApply (lifting.wp_cmpxchg_fail with "[$]"); [naive_solver|done|done].

  Ltac solve_cmpxchg_suc :=
    iIntros "* %Heq % Hl HΦ"; subst; rewrite typed_pointsto_unseal /= !go.into_val_unfold;
      iApply (lifting.wp_cmpxchg_suc with "[$]"); done.

  Ltac solve_wp_atomic_load :=
    iIntros "* Hl HΦ"; rewrite typed_pointsto_unseal /= !go.into_val_unfold;
    iApply (lifting.wp_load with "[$]"); done.

  Ltac solve_wp_atomic_swap :=
    iIntros "* Hl HΦ"; rewrite typed_pointsto_unseal /= !go.into_val_unfold;
    iApply (lifting.wp_atomic_swap with "[$]"); done.

  Ltac solve_atomic_wps :=
    split; rewrite !go.into_val_unfold;
    [solve_cmpxchg_fail | solve_cmpxchg_suc | solve_wp_atomic_load | solve_wp_atomic_swap ].

  #[global] Instance atomic_wps_uint64 : AtomicWps w64.
  Proof. solve_atomic_wps. Qed.
  #[global] Instance atomic_wps_uint32 : AtomicWps w32.
  Proof. solve_atomic_wps. Qed.
  #[global] Instance atomic_wps_uint16 : AtomicWps w16.
  Proof. solve_atomic_wps. Qed.
  #[global] Instance atomic_wps_uint8 : AtomicWps w8.
  Proof. solve_atomic_wps. Qed.
  #[global] Instance atomic_wps_bool : AtomicWps bool.
  Proof. solve_atomic_wps. Qed.

End goose_lang.

Section tac_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
    {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

  Class PointsToAccess {V} `{!TypedPointsto V}
    (l : loc) (v : V) dq (P : iProp Σ) (P' : V → iProp Σ) : Prop :=
    {
      points_to_acc : P -∗ l ↦{dq} v ∗ (∀ v', l ↦{dq} v' -∗ P' v');
      points_to_update_eq : P' v ⊣⊢ P;
    }.

  Global Instance points_to_access_trivial {V} l (v : V) `{!TypedPointsto V} dq
    : PointsToAccess l v dq (l ↦{dq} v)%I (λ v', l ↦{dq} v')%I.
  Proof. constructor; [eauto with iFrame|done]. Qed.

  Lemma tac_wp_load {V t} `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
    K (l : loc) (v : V) Δ s E i dq Φ is_pers
    `{!PointsToAccess l v dq P P'} :
    envs_lookup i Δ = Some (is_pers, P)%I →
    envs_entails Δ (WP (fill K (Val #v)) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (load t #l)) @ s; E {{ Φ }}).
  Proof using Type*.
    rewrite envs_entails_unseal => ? HΦ.
    rewrite envs_lookup_split //.
    iIntros "[H Henv]".
    destruct is_pers; simpl.
    - iDestruct "H" as "#H".
      iDestruct (points_to_acc with "H") as "[H' _]".
      wp_apply (wp_load with "[$]"). iIntros "?".
      iApply HΦ. iApply "Henv". iFrame "#".
    - iDestruct (points_to_acc with "H") as "[H Hclose]".
      wp_apply (wp_load with "[$]"). iIntros "?".
      iApply HΦ. iApply "Henv".
      iSpecialize ("Hclose" with "[$]").
      rewrite points_to_update_eq. iFrame.
  Qed.

  Lemma tac_wp_store {V t} `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
    K (l : loc) (v v' : V) Δ Δ' s E i Φ
    `{!PointsToAccess l v (DfracOwn 1) P P'} :
    envs_lookup i Δ = Some (false, P)%I →
    envs_simple_replace i false (Esnoc Enil i (P' v')) Δ = Some Δ' →
    envs_entails Δ' (WP fill K (Val #()) @ s ; E {{ Φ }}) →
    envs_entails Δ (WP (fill K (store t #l (Val #v'))) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ?? HΦ.
    rewrite envs_simple_replace_sound // /=.
    iIntros "[H Henv]".
    iDestruct (points_to_acc with "H") as "[H Hclose]".
    wp_apply (wp_store with "[$]"). iIntros "H".
    iSpecialize ("Hclose" with "[$]"). iApply HΦ.
    iApply "Henv". iFrame.
  Qed.

  Lemma tac_wp_alloc K
    `{!TypedPointsto V} `{!ZeroVal V} `{!IntoValTyped V t} (v : V) Δ stk E Φ :
    (∀ l, envs_entails Δ (l ↦ v -∗ WP (fill K (Val #l)) @ stk; E {{ Φ }})) →
    envs_entails Δ (WP fill K (alloc t #v) @ stk; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hwp.
    iIntros "Henv".
    wp_apply wp_alloc. iIntros.
    by iApply (Hwp with "[$]").
  Qed.

End tac_lemmas.

Ltac2 tc_solve_many () := solve [ltac1:(typeclasses eauto)].

Ltac2 ectx_simpl () := cbv [fill flip foldl ectxi_language.fill_item goose_ectxi_lang fill_item].

Ltac2 wp_load_visit e k :=
  Control.once_plus (fun () => Std.unify e '(load _ (Val _)))
         (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_load $k) > [tc_solve_many ()| ltac1:(iAssumptionCore) | ectx_simpl ()])
    (fun _ => Control.backtrack_tactic_failure "wp_load: could not find a points-to in context covering the address")
.

Ltac2 wp_load () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_load_visit)
                                                        "wp_load: could not find load_ty"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_load: not a wp"
  end.

Ltac2 wp_store_visit e k :=
  Control.once_plus (fun () => (Std.unify e '(store _ _ (Val _))))
         (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => eapply (tac_wp_store $k) > [tc_solve_many ()| ltac1:(iAssumptionCore)
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
  Control.once_plus (fun () => Std.unify e '(alloc _ (Val (#_))))
    (fun _ => Control.zero Walk_expr_more);
  Control.once_plus (fun _ => apply (tac_wp_alloc $k); ectx_simpl ())
    (fun _ => Control.backtrack_tactic_failure "wp_alloc: failed to apply tac_wp_alloc (maybe no IntoValTyped instance?)")
.

Ltac2 wp_alloc () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ ?e _) ] => wp_walk_unwrap (fun () => walk_expr e wp_alloc_visit)
                                                        "wp_alloc: could not find [alloc]"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_alloc: not a wp"
  end.

Ltac2 wp_alloc_auto_visit e k :=
  lazy_match! e with
  (* Manually writing out [let: ?var_name := (ref_ty _ (Val _)) in ?e1] to get
     pattern matching to work. *)
  | (App (Rec BAnon (BNamed ?var_name) ?e1) (App (Val (alloc _)) (Val (#_)))) =>
      let let_expr1 := '(Rec BAnon (BNamed $var_name) $e1) in
      let ptr_name := Std.eval_vm None constr:($var_name +:+ "_ptr") in
      let k := constr:(@AppRCtx _ $let_expr1 :: $k) in
      Control.once_plus (fun _ => apply (tac_wp_alloc $k); ectx_simpl ())
        (fun _ => Control.backtrack_tactic_failure "wp_alloc_auto: failed to apply tac_wp_alloc");
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
                                                        "wp_alloc_auto: could not find [alloc]"
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
