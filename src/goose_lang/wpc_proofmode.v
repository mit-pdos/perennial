From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import atomic.
From Perennial.goose_lang Require Import tactics lifting array.
From Perennial.goose_lang Require Import notation.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wpc_expr_eval `{ffi_sem: ext_semantics} `{!ffi_interp ffi}
      `{!heapG Σ, !crashG Σ} Δ (s: stuckness) (k: nat) E1 E2 Φ (Φc: iProp Σ) e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WPC e' @ s; k; E1; E2 {{ Φ }} {{ Φc }}) → envs_entails Δ (WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}).
Proof. by intros ->. Qed.

Tactic Notation "wpc_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?E2 ?e ?Q1 ?Q2) =>
    eapply tac_wpc_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  end.

Lemma tac_wpc_pure `{ffi_sem: ext_semantics} `{!ffi_interp ffi}
      `{!heapG Σ, !crashG Σ} Δ Δ' s k E1 E2 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' Φc →
  (envs_entails Δ' Φc → envs_entails Δ' (WPC e2 @ s; k; E1; E2 {{ Φ }} {{ Φc }})) →
  envs_entails Δ (WPC e1 @ s; k; E1; E2 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq=> ??? Hcrash HΔ'.
  rewrite -wpc_pure_step_later //. apply and_intro; auto.
  - rewrite into_laterN_env_sound /=.
    rewrite HΔ' //.
  - rewrite into_laterN_env_sound /= -Hcrash //.
Qed.

Lemma tac_wpc_value `{ffi_sem: ext_semantics} `{!ffi_interp ffi}
      `{!heapG Σ, !crashG Σ} Δ s k E1 E2 Φ Φc v :
  envs_entails Δ (Φ v) →
  envs_entails Δ (Φc) →
  envs_entails Δ (WPC (Val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq -wpc_value => H1 H2.
  apply and_intro.
  - rewrite H1. eauto.
  - rewrite H2. iIntros. iModIntro; iApply fupd_mask_weaken; eauto; try set_solver+.
Qed.

Ltac wpc_expr_simpl := wpc_expr_eval simpl.

Ltac wpc_value_head :=
  first [eapply tac_wpc_value ].

Ltac wpc_finish H :=
  wpc_expr_simpl;      (* simplify occurences of subst/fill *)
  try (wpc_value_head; try apply H);  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.         (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
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

Tactic Notation "wpc_pure" open_constr(efoc) simple_intropattern(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?E2 ?e ?Q ?Qc) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wpc_pure _ _ _ _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      | try (apply H)                 (* crash condition, try to re-use existing proof *)
      | first [ intros H || intros _]; wpc_finish H (* new goal *)
      ])
    || fail "wpc_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wpc_pure: not a 'wpc'"
  end.

Ltac crash_case :=
  try lazymatch goal with
      | [ |- envs_entails (Envs ?ienv ?senv _) ?Φc ] =>
        is_var Φc;
        lazymatch senv with
        | context[Esnoc _ ?H ((_ -∗ Φc) ∧ _)%I] => iApply H
        end
      end.

Ltac wpc_pures :=
  iStartProof;
  let Hcrash := fresh "Hcrash" in
  wpc_pure _ Hcrash; [crash_case ..  | repeat (wpc_pure _ Hcrash; []); clear Hcrash].

Lemma tac_wpc_bind `{ffi_sem: ext_semantics} `{!ffi_interp ffi}
      `{!heapG Σ, !crashG Σ} K Δ s k E1 E2 Φ Φc e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WPC e @ s; k; E1; E2 {{ v, WPC f (Val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }} }} {{ Φc }})%I →
  envs_entails Δ (WPC fill K e @ s; k; E1; E2 {{ Φ }} {{ Φc }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wpc_bind. Qed.

Ltac wpc_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wpc_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wpc_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?E2 ?e ?Q1 ?Q2) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wpc_bind_core K)
    || fail "wpc_bind: cannot find" efoc "in" e
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => fail "wpc_bind: 'wp', not a 'wpc'"
  | _ => fail "wpc_bind: not a 'wpc'"
  end.

Tactic Notation "wpc_atomic" :=
  iApply wpc_atomic_no_mask;
  iSplit; [ crash_case | ].

(** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
Tactic Notation "wpc_apply_core" open_constr(lem) tactic(tac) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wpc ?s ?k ?E1 ?E2 ?e ?Q ?Qc) =>
      reshape_expr e ltac:(fun K e' =>
        wpc_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wpc_apply: not a 'wpc'"
    end).
Tactic Notation "wpc_apply" open_constr(lem) :=
  wpc_apply_core lem (fun H => iApplyHyp H; try iNext).

Tactic Notation "wpc_if_destruct" :=
  match goal with
  | |- envs_entails _ (wpc _ _ _ _ (if: Val $ LitV $ LitBool ?cond then _ else _) _ _) =>
    destruct cond eqn:?;
             repeat match goal with
                    | [ H: context[(word.ltu ?x ?y)] |- _ ] => rewrite (word.unsigned_ltu x y) in H
                    | [ H: (?x <? ?y)%Z = true |- _ ] => apply Z.ltb_lt in H
                    | [ H: (?x <? ?y)%Z = false |- _ ] => apply Z.ltb_ge in H
                    | [ H: (?x <=? ?y)%Z = true |- _ ] => apply Z.leb_le in H
                    | [ H: (?x <=? ?y)%Z = false |- _ ] => apply Z.leb_gt in H
                    end
  end.

(* TODO: this works, but maybe we can do better *)
Tactic Notation "iLeft" "in" constr(H) := let pat := constr:(intro_patterns.IList [[intro_patterns.IIdent H; intro_patterns.IDrop]]) in
                                          iDestruct H as pat.
Tactic Notation "iRight" "in" constr(H) := let pat := constr:(intro_patterns.IList [[intro_patterns.IDrop; intro_patterns.IIdent H]]) in
                                           iDestruct H as pat.

(* TODO: fix this to use a tac_ theorem; look at tac_wp_allocN for an example of
env splitting *)

Tactic Notation "wpc_frame" constr(pat) :=
  iApply wp_wpc_frame';
  iSplitL pat; [ iAccu | iSplitR; [ iModIntro | ] ].
