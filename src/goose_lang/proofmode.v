From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export environments.
From Perennial.Helpers Require Export ipm.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.

Lemma tac_wp_pure `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "H". iApply (laterN_mono with "H").
  by iIntros.
Qed.

Lemma tac_wp_pure_no_later `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      Δ s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "$".
  iApply laterN_intro. by iIntros.
Qed.

Lemma tac_wp_pure_gen_cred `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (£ n -∗ WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.

Lemma tac_wp_pure_no_later_gen_cred `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      Δ s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (£ n -∗ WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "$".
Qed.

Class PureWp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
  φ (e: expr) (v': val) :=
  pure_wp_wp : ∀ stk E Φ (H:φ), ▷ Φ v' -∗ WP e @ stk; E {{ Φ }}.

Global Hint Mode PureWp - - - - - - - - ! - : typeclass_instances.

Lemma tac_wp_pure_wp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      Δ Δ' s E K (e1: expr) (v2: val) φ Φ :
  PureWp φ e1 v2 →
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K (Val v2)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hstep ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'.
  iIntros "H". iApply wp_bind. iApply Hstep; [ done | ].
  iApply "H".
Qed.

Lemma tac_wp_value_noncfupd `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_value. Qed.
Lemma tac_wp_value_fupd `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ} Δ s E Φ v :
  envs_entails Δ (|NC={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ v, |={E}=> Φ v }})%I.
Proof.
  rewrite envs_entails_unseal=> ->. rewrite wp_value_fupd.
  iIntros "H".
  iApply (wp_wand with "H"); auto.
Qed.
Lemma tac_wp_value `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ} Δ s E Φ v :
  envs_entails Δ (|NC={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. rewrite wp_value_fupd //. Qed.

Ltac wp_expr_simpl := wp_expr_eval simpl.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a [ncfupd], do not add a second one.
  If it is a [fupd], upgrade that to an [ncfupd].
  But otherwise, *do* add a [ncfupd]. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, ncfupd ?E _ _)) =>
      eapply tac_wp_value_noncfupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_noncfupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_fupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  end.

Lemma tac_wp_true_elim Σ Δ (P: iProp Σ) :
  envs_entails Δ P ->
  envs_entails Δ (bi_wand (bi_pure True) P).
Proof. rewrite envs_entails_unseal=> ->. iIntros "$ _ //". Qed.

Lemma tac_wp_true Σ (Δ: envs (iPropI Σ)) :
  envs_entails Δ (bi_pure True).
Proof. done. Qed.

Ltac solve_bi_true :=
  try lazymatch goal with
      | |- envs_entails _ (bi_pure True) => apply tac_wp_true
      | |- envs_entails _ (bi_wand (bi_pure True) _)  => apply tac_wp_true_elim
      end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).


(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure_later" tactic3(filter) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wp_pure _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chose to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_pure_no_later" tactic3(filter) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wp_pure_no_later _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |wp_finish                      (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* smart version that decides which one to use *)
Tactic Notation "wp_pure_smart" tactic3(filter) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?envs _ =>
    lazymatch envs with
    | context[Esnoc _ _ (bi_later _)] => wp_pure_later filter
    | _ => wp_pure_no_later filter
    end
  end.
Tactic Notation "wp_pure" open_constr(efoc) :=
  wp_pure_smart ltac:(fun e => unify e efoc).

(* This needs to detect all things that [wp_pures] should reduce. *)
Ltac wp_pure_filter e' :=
  (* For Beta-redices, we do *syntactic* matching only, to avoid unfolding
     definitions. This matches the treatment for [pure_beta] via [AsRecV]. *)
  first [ lazymatch e' with (App (Val (RecV _ _ _)) (Val _)) => idtac end
        | let _ := constr:(_:WpPureExecCandidate e') in idtac
        | eunify e' (rec: _ _ := _)%E
        | eunify e' (InjL (Val _))
        | eunify e' (InjR (Val _))
        | eunify e' (Val _, Val _)%E
        | eunify e' (Fst (Val _))
        | eunify e' (Snd (Val _))
        | eunify e' (if: (Val _) then _ else _)%E
        | eunify e' (Case (Val _) _ _)
        | eunify e' (UnOp _ (Val _))
        | eunify e' (BinOp _ (Val _) (Val _))
        | eunify e' (TotalLe (Val _) (Val _))
    ].

Tactic Notation "wp_pure_later_credit" tactic3(filter) "as" constr(credName) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wp_pure_gen_cred _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |(iIntros credName || fail 4 "wp_pure: unalbe to introduce hypothesis for credit");
       (* XXX(upamanyu): 4 is chosen to be one more than 3, but I don't know what it really does *)
       wp_finish                      (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chose to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_pure_no_later_credit" tactic3(filter) "as" constr(credName) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wp_pure_no_later_gen_cred _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      | (iIntros credName || fail 4 "wp_pure: unable to introduce hypothesis for credit");
         wp_finish                    (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_pure_smart_credit" tactic3(filter) "as" constr(credName) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?envs _ =>
    lazymatch envs with
    | context[Esnoc _ _ (bi_later _)] => wp_pure_later_credit filter as credName
    | _ => wp_pure_no_later_credit filter as credName
    end
  end.
Tactic Notation "wp_pure1_credit" constr(credName) :=
  iStartProof; wp_pure_smart_credit wp_pure_filter as credName.

Ltac wp_pure_steps1 :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_pure_wp _ _ _ _ K e');
          [tc_solve (* PureWpSteps *)
          |try solve_vals_compare_safe (* pure side condition *)
          |tc_solve (* MaybeIntoLaterNEnvs *)
          |wp_finish (* new goal *)
          ]
      ) || fail "wp_pure_steps: cannot find redex pattern"
  | _ => fail "wp_pure_steps1: not a 'wp'"
  end.

Ltac wp_pure1 :=
  iStartProof; wp_pure_smart wp_pure_filter.
Ltac wp_pures :=
  iStartProof;
  lazymatch goal with
    | |- envs_entails ?envs (wp ?s ?E (Val ?v) ?Q) => wp_finish
    | |- _ =>
      (* The `;[]` makes sure that no side-condition
                             magically spawns. *)
      (* TODO: do this in one go, without [repeat]. *)
      try ((first [ wp_pure1 | wp_pure_steps1 ]; []);
      repeat (
          first [ wp_pure_no_later wp_pure_filter | wp_pure_steps1 ];
          []))
  end.

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  pose proof AsRecV_recv as H;
  wp_pure (App (Val (RecV _ _ _)) (Val _));
  clear H.

Theorem inv_litv {ext:ffi_syntax} l1 l2 : LitV l1 = LitV l2 -> l1 = l2.
Proof.
  inversion 1; auto.
Qed.

(* TODO: why are these notations instead of Ltac? *)
Tactic Notation "wp_if" := wp_pure (If (Val _) _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst (Val _)) || wp_pure (Snd (Val _)).
Tactic Notation "wp_case" := wp_pure (Case (Val _) _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL (Val _)) || wp_pure (InjR (Val _)).
Tactic Notation "wp_pair" := wp_pure (Pair (Val _) (Val _)).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).
(* TODO: get rid of these old aliases *)
Ltac wp_step := try wp_pures.
Ltac wp_steps := try wp_pures.
Ltac wp_call := wp_lam; wp_steps.

Lemma tac_wp_bind `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseLocalGS Σ, !gooseGlobalGS Σ}
    K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

Lemma base_lit_inv (l1 l2: base_lit) :
  l1 = l2 →
  match l1, l2 with
  | LitInt n1, LitInt n2 => n1 = n2
  | LitInt32 n1, LitInt32 n2 => n1 = n2
  | LitBool b1, LitBool b2 => b1 = b2
  | LitByte n1, LitByte n2 => n1 = n2
  | LitString s1, LitString s2 => s1 = s2
  | LitUnit, LitUnit => True
  | LitPoison, LitPoison => True
  | LitLoc x1, LitLoc x2 => x1 = x2
  | LitProphecy p1, LitProphecy p2 => p1 = p2
  | _, _ => False
  end.
Proof.
  destruct l1, l2; inversion 1; auto.
Qed.

Tactic Notation "wp_if_destruct" :=
  wp_pures;
  (try wp_bind (If _ _ _));
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (if: Val $ LitV $ LitBool ?cond then _ else _) _) =>
    destruct cond eqn:?;
    repeat match goal with
           | [ H: (?x <? ?y)%Z = true |- _ ] => apply Z.ltb_lt in H
           | [ H: (?x <? ?y)%Z = false |- _ ] => apply Z.ltb_ge in H
           | [ H: (?x <=? ?y)%Z = true |- _ ] => apply Z.leb_le in H
           | [ H: (?x <=? ?y)%Z = false |- _ ] => apply Z.leb_gt in H
           | [ H: bool_decide _ = true |- _ ] => apply bool_decide_eq_true_1 in H
           | [ H: bool_decide _ = false |- _ ] => apply bool_decide_eq_false_1 in H
           (* Match regular [negb], not proofmode [negb] (which is not usually in scope,
              but in this file we imported [proofmode.base] via [proofmode.coq_tactics]). *)
           | [ H: Datatypes.negb _ = true |- _ ] => apply negb_true_iff in H; subst
           | [ H: Datatypes.negb _ = false |- _ ] => apply negb_false_iff in H; subst
           | [ H: LitV _ = LitV _ |- _ ] => apply inv_litv in H
           | [ H: @eq base_lit _ _ |- _ ] => apply base_lit_inv in H; simpl in H; subst
           end;
    [ wp_if_true | wp_if_false ]
  | |- envs_entails _ (wp _ _ ?e _) =>
    fail "goal is for" e "which is not an if expression"
  | _ => fail "goal is not a wp"
  end.

(** Heap tactics *)
Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wp_load Δ Δ' s E i K l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  rewrite -wp_bind. eapply wand_apply; first by apply bi.wand_entails, wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_load_persistent Δ s E i K l v Φ :
  envs_lookup i Δ = Some (true, l ↦□ v)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΦ.
  rewrite -wp_bind. eapply wand_apply; first by apply bi.wand_entails, wp_load.
  rewrite envs_lookup_split //; simpl.
  iIntros "[#Hp Henvs]".
  iSplitR; auto.
  iIntros "!> _".
  iApply HΦ.
  iApply ("Henvs" with "Hp").
Qed.

Lemma tac_wp_cmpxchg Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  vals_compare_safe v v1 →
  (v = v1 →
   envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})) →
  (v ≠ v1 →
   envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???? Hsuc Hfail.
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -wp_bind. eapply wand_apply.
    { eapply bi.wand_entails, wp_cmpxchg_suc; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wp_bind. eapply wand_apply.
    { eapply bi.wand_entails, wp_cmpxchg_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wp_cmpxchg_fail Δ Δ' s E i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?????.
  rewrite -wp_bind. eapply wand_apply; first by apply bi.wand_entails, wp_cmpxchg_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cmpxchg_suc Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  v = v1 → vals_compare_safe v v1 →
  envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??????; subst.
  rewrite -wp_bind. eapply wand_apply.
  { eapply bi.wand_entails, wp_cmpxchg_suc; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

(** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
Tactic Notation "wp_apply_core" open_constr(lem) tactic(tac) :=
  wp_pures;
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).
Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl; solve_bi_true).
(*
(** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise.  The second one additionaly does some framing: it gets rid of [Hs] from
the context, which is intended to be the non-laterable assertions that iAuIntro
would choke on.  You get them all back in the continuation of the atomic
operation. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; last iAuIntro).
Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  wp_apply_core lem (fun H => iApply wp_frame_wand_l; iSplitL Hs; [iAccu|iApplyHyp H; last iAuIntro]).
*)

Lemma wand_curry_1 {PROP: bi} (P Q R: PROP) :
  (P -∗ Q -∗ R) → (P ∗ Q -∗ R).
Proof.
  rewrite wand_curry //.
Qed.

(* apply a WP lemma without providing it the precondition resources; instead,
produce goals Δ ⊢ pre ∗ ?r (with the entire original context) and
 ?r -∗ post -∗ WP e' {{ .. }} (with no context).

This allows to prove the precondition with all resources, use [iNamedAccu] to
solve [?r] with all the unused resources, and continue the proof in the other
goal with [iNamed 1] using those resources.
 *)
Tactic Notation "wp_apply_delay" open_constr(lem) :=
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApply wand_curry_1; [ eapply lem | iSplitDelay ]) ||
      fail "wp_apply: cannot apply" lem
    | _ => fail "wp_apply: not a 'wp'"
    end.

Tactic Notation "wp_untyped_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_untyped_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
        |fail 1 "wp_untyped_load: cannot find 'Load' in" e];
      [tc_solve
      |solve_pointsto ()
      |wp_finish] ) ||
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_persistent _ _ _ _ K))
        |fail 1 "wp_untyped_load: cannot find 'Load' in" e];
      [solve_pointsto ()
      |wp_finish] )
  | _ => fail "wp_untyped_load: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg _ _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |try solve_vals_compare_safe
    |intros H1; wp_finish
    |intros H2; wp_finish]
  | _ => fail "wp_cmpxchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_fail" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_fail: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_fail _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_fail: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_suc" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_suc _ _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_suc: not a 'wp'"
  end.
