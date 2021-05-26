From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import atomic.
From Perennial.goose_lang Require Import lifting proofmode.
From Perennial.goose_lang.lib Require Import struct.struct.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant.
From Perennial.Helpers Require Export ipm NamedProps ProofCaching.
Set Default Proof Using "Type".
Import uPred.

Lemma wpc_fork `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ, !crashG Σ} s k E1 e Φ Φc :
  ▷ WPC e @ s; k; ⊤ {{ _, True }} {{ True }} -∗ (Φc ∧ ▷ Φ (LitV LitUnit)) -∗
                      WPC Fork e @ s; k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "He HΦ". iApply wpc_lift_head_step; [done|].
  iSplit; last first.
  {  iDestruct "HΦ" as "(HΦc&_)". eauto. }
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first by set_solver+.
  iModIntro. iNext. iSplit.
  { iPureIntro; econstructor; do 4 eexists. constructor. constructor. eauto. }
   iIntros (v2 σ2 g2 efs Hstep). apply head_step_atomic_inv in Hstep; [ | by inversion 1 ]. rewrite /head_step /= in Hstep.
  inversion Hstep as [??? Heq]. inversion Heq; subst.
  iMod "Hclose". iFrame.
  iMod (global_state_interp_le with "Hg") as "$".
  { apply step_count_next_incr. }
  iModIntro => //=. rewrite right_id.
  iApply wpc_value; iSplit.
  - by iDestruct "HΦ" as "(_&$)".
  - iDestruct "HΦ" as "(?&_)". eauto.
Qed.

Lemma tac_wpc_expr_eval `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ} Δ (s: stuckness) (k: nat) E1 Φ (Φc: iProp Σ) e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WPC e' @ s; k; E1 {{ Φ }} {{ Φc }}) → envs_entails Δ (WPC e @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof. by intros ->. Qed.

Tactic Notation "wpc_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q1 ?Q2) =>
    notypeclasses refine (tac_wpc_expr_eval _ _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  end.

Lemma tac_wpc_pure_ctx `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ, !crashG Σ} Δ Δ' s k E1 K e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ (Φc) →
  (envs_entails Δ (Φc) → envs_entails Δ' (WPC (fill K e2) @ s; k; E1 {{ Φ }} {{ Φc }})) →
  envs_entails Δ (WPC (fill K e1) @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq=> ??? Hcrash HΔ'.
  pose proof @pure_exec_fill.
  rewrite -wpc_pure_step_later //. apply and_intro; auto.
  rewrite into_laterN_env_sound /=.
  rewrite HΔ' //.
Qed.

Lemma tac_wpc_pure_no_later_ctx `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ, !crashG Σ}
      Δ s k E1 K e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  envs_entails Δ Φc →
  (envs_entails Δ Φc → envs_entails Δ (WPC (fill K e2) @ s; k; E1 {{ Φ }} {{ Φc }})) →
  envs_entails Δ (WPC (fill K e1) @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq=> ?? Hcrash HΔ'.
  pose proof @pure_exec_fill.
  specialize (HΔ' Hcrash).
  rewrite -wpc_pure_step_later //. apply and_intro; auto.
  - iIntros "Henv".
    iModIntro.
    iApply HΔ'; iAssumption.
Qed.

Lemma tac_wpc_value `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ} Δ s k E1 Φ Φc v :
  envs_entails Δ (|NC={E1}=> Φ v) →
  envs_entails Δ Φc →
  envs_entails Δ (WPC (Val v) @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq -wpc_value => H1 H2.
  apply and_intro.
  - rewrite H1. eauto.
  - rewrite H2. iIntros. eauto.
Qed.
Lemma tac_wpc_value_fupd `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ} Δ s k E1 Φ Φc v :
  envs_entails Δ (|NC={E1}=> Φ v) →
  envs_entails Δ Φc →
  envs_entails Δ (WPC (Val v) @ s; k; E1 {{ v, |={E1}=> Φ v }} {{ Φc }})%I.
Proof.
  rewrite envs_entails_eq -wpc_value => H1 H2.
  apply and_intro.
  - rewrite H1. iIntros ">?". eauto.
  - rewrite H2. iIntros. eauto.
Qed.
Lemma tac_wpc_value_noncfupd `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ} Δ s k E1 Φ Φc v :
  envs_entails Δ (Φ v) →
  envs_entails Δ Φc →
  envs_entails Δ (WPC (Val v) @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq -wpc_value => H1 H2.
  apply and_intro.
  - rewrite H1. eauto.
  - rewrite H2. iIntros. eauto.
Qed.

Ltac wpc_expr_simpl := wpc_expr_eval simpl.

(** Simplify the goal if it is [WPC] of a value.
  If the postcondition already allows a [ncfupd], do not add a second one.
  If it is a [fupd], upgrade that to an [ncfupd].
  But otherwise, *do* add a [ncfupd]. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wpc_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E (Val _) (λ _, ncfupd ?E _ _) _) =>
      eapply tac_wpc_value_noncfupd
  | |- envs_entails _ (wpc ?s ?k ?E (Val _) (λ _, wpc _ _ ?E _ _ _) _) =>
      eapply tac_wpc_value_noncfupd
  | |- envs_entails _ (wpc ?s ?k ?E (Val _) (λ _, fupd ?E _ _) _) =>
      eapply tac_wpc_value_fupd
  | |- envs_entails _ (wpc ?s ?k ?E (Val _) _ _) =>
      eapply tac_wpc_value
  end.

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

Tactic Notation "iCache" "with" constr(Hs) :=
  lazymatch goal with
  | [ |- envs_entails _ (wpc _ _ _ _ _ ?Φc) ] =>
        iCache_go Φc Hs "#?"
  | _ => fail 1 "not a wpc goal"
  end.

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)

Tactic Notation "wpc_pure_later" tactic3(filter) "as" simple_intropattern(H) :=
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q ?Qc) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wpc_pure_ctx _ _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      | try (apply H)                 (* crash condition, try to re-use existing proof *)
      | first [ intros H || intros _]; wpc_finish H (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chosen to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   )
    || fail "wpc_pure_later: cannot find redex pattern"
  | _ => fail "wpc_pure_later: not a 'wpc'"
  end.

Tactic Notation "wpc_pure_no_later" tactic3(filter) "as" simple_intropattern(H) :=
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q ?Qc) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      filter e';
      first [ eapply (tac_wpc_pure_no_later_ctx _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      | try (apply H)                 (* crash condition, try to re-use existing proof *)
      | first [ intros H || intros _]; wpc_finish H (* new goal *)
      ] | fail 3 "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chosen to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   )
    || fail "wpc_pure: cannot find redex pattern"
  | _ => fail "wpc_pure: not a 'wpc'"
  end.

Tactic Notation "wpc_pure_smart" tactic3(filter) "as" simple_intropattern(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?envs _ =>
    lazymatch envs with
    | context[Esnoc _ _ (bi_and _ (bi_later _))] => wpc_pure_later filter as H
    | context[Esnoc _ _ (bi_later _)] => wpc_pure_later filter as H
    | _ => wpc_pure_no_later filter as H
    end
  end.
Tactic Notation "wpc_pure" open_constr(efoc) simple_intropattern(H) :=
  wpc_pure_smart ltac:(fun e => unify e efoc) as H.

Ltac crash_case :=
  try lazymatch goal with
      | [ |- envs_entails (Envs ?ienv ?senv _) ?Φc ] =>
        is_var Φc;
        lazymatch senv with
        | context[Esnoc _ ?H ((_ -∗ Φc) ∧ _)%I] => iLeft in H; iApply H
        | context[Esnoc _ ?H (Φc ∧ _)%I] => iLeft in H; iExact H
        end
      end.

Tactic Notation "wpc_pure1" simple_intropattern(H) :=
  iStartProof;
  wpc_pure_smart wp_pure_filter as H.
Ltac wpc_pures :=
  iStartProof;
  let Hcrash := fresh "Hcrash" in
  lazymatch goal with
    | |- envs_entails ?envs (wpc ?s ?k ?E1 (Val _) ?Q ?Qc) => wpc_finish Hcrash
    | |- _ =>
      wpc_pure1 Hcrash;
      [try iFromCache .. | repeat (wpc_pure_no_later wp_pure_filter as Hcrash; []); clear Hcrash]
  end.

Lemma tac_wpc_bind `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ, !crashG Σ} K Δ s k E1 Φ Φc e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WPC e @ s; k; E1 {{ v, WPC f (Val v) @ s; k; E1 {{ Φ }} {{ Φc }} }} {{ Φc }})%I →
  envs_entails Δ (WPC fill K e @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wpc_bind. Qed.

Lemma tac_wpc_wp_frame `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ, !crashG Σ} Δ d js s k E1 e (Φ: _ -> iProp Σ) (Φc: iProp Σ) :
  match envs_split d js Δ with
  | Some (Δ1, Δ2) => envs_entails Δ1 Φc ∧
                     envs_entails Δ2 (WP e @ s; E1
                             {{ v, (env_to_named_prop Δ1.(env_spatial) -∗ Φ v)%I }})
  | None => False
  end ->
  envs_entails Δ (WPC e @ s; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  destruct (envs_split d js Δ) as [[Δ1 Δ2]|] eqn:Hsplit; [ | contradiction ].
  rewrite envs_entails_eq=> Hentails.
  destruct Hentails as [HΦc Hwp].
  rewrite (envs_split_sound _ _ _ _ _ Hsplit).
  rewrite {}Hwp.
  iIntros "[HΦc' Hwp]".
  iApply (wp_wpc_frame' _ _ _ _ _ (Φc) (of_envs Δ1)).
  iSplitR "Hwp".
  { iSplit; iFrame. by iApply HΦc. }
  iApply (wp_mono with "Hwp"); cbv beta.
  iIntros (v) "Hwand HΔ".
  iApply "Hwand".
  iDestruct (envs_clear_spatial_sound with "HΔ") as "[Hp Hs]".
  rewrite env_to_named_prop_sound.
  iAssumption.
Qed.

(* combines using [wpc_frame Hs] with [iFromCache], simultaneously framing and
   proving the crash condition using a cache *)
Lemma tac_wpc_wp_frame_cache `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
      `{!heapGS Σ, !crashG Σ} (Φc: iProp Σ) i (* name of cache *) (c: cache Φc)
      Δ stk k E1 e (Φ: _ → iProp Σ)  :
  envs_lookup i Δ = Some (true, cached c) →
  match envs_split Left c.(cache_names) Δ with
  | Some (Δ1, Δ2) =>
    (* we use the cache hypotheses [Δ1] for the crash condition... *)
    Δ1.(env_spatial) = c.(cache_prop) ∧
    envs_entails Δ2 (* and the remainder [Δ2] to prove a wp for the same [e] *)
      (WP e @ stk; E1 {{ v, (env_to_named_prop Δ1.(env_spatial) -∗ Φ v)%I }})
  | None => False
  end →
  envs_entails Δ (WPC e @ stk; k; E1 {{ Φ }} {{ Φc }}).
Proof.
  rewrite envs_entails_eq=> Hcache H.
  destruct (envs_split Left (cache_names c) Δ) as [[Δ1 Δ2]|] eqn:Hsplit;
    [ | contradiction ].
  destruct H as (Hcenv & Hwp).
  iIntros "HΔ".
  iDestruct (envs_lookup_intuitionistic_sound _ _ _ Hcache
               with "HΔ") as "[#Hcache HΔ]".
  rewrite (envs_split_sound _ _ _ _ _ Hsplit).
  iDestruct "HΔ" as "[Hcrash HΔ2]".
  iApply wp_wpc_frame'.
  iSplitL "Hcrash".
  { iSplit; last iApply "Hcrash".
    iApply (cached_elim with "Hcache Hcrash"); auto. }
  iDestruct (Hwp with "HΔ2") as "Hwp".
  iApply (wp_mono with "Hwp"); cbv beta.
  iIntros (v) "Hwand HΔ".
  iApply "Hwand".
  iDestruct (envs_clear_spatial_sound with "HΔ") as "[Hp Hs]".
  rewrite env_to_named_prop_sound.
  iAssumption.
Qed.

Tactic Notation "wpc_frame" :=
  lazymatch goal with
  | [ |- envs_entails (Envs ?Γp _ _) (wpc _ _ _ _ _ ?Φc) ] =>
    first [ match Γp with
            | context[Esnoc _ ?i (@cached _ Φc ?c)] =>
              apply (tac_wpc_wp_frame_cache Φc i c);
              [ reflexivity (* lookup should always succeed, found by context match *)
              | reduction.pm_reduce; split;
                [ (* cache hypothesis match *)
                  reflexivity
                | (* remaining wp *)
                cached_reduce
                ]
              ]
            end
          | fail 1 "no cache for crash condition" Φc
          ]
  | _ => fail 1 "wpc_frame: not a wpc"
  end.

(** [pat] is the original pattern, for error messages *)
Ltac wpc_frame_go pat d js :=
  apply (tac_wpc_wp_frame _ d js);
  [ reduction.pm_reduce;
    lazymatch goal with
    | |- False => fail "wpc_frame:" pat "not found"
    | _ =>
      split; [ try iFromCache (* crash condition from framed hyps *)
             | cached_reduce (* remaining wp *) ]
    end
  ].

Ltac wpc_frame_pat d pat :=
  let js := (eval cbv in (INamed <$> words pat)) in
  wpc_frame_go pat d js.

Tactic Notation "wpc_frame" constr(pat) := wpc_frame_pat base.Left pat.
Tactic Notation "wpc_frame_compl" constr(pat) := wpc_frame_pat base.Right pat.

Tactic Notation "wpc_rec" simple_intropattern(H) :=
  let HAsRecV := fresh in
  pose proof AsRecV_recv as HAsRecV;
  wpc_pure (App (Val (RecV _ _ _)) (Val _)) H;
  clear HAsRecV.
Tactic Notation "wpc_let" simple_intropattern(H) := wpc_pure (Rec BAnon (BNamed _) _) H; wpc_rec H.

Ltac wpc_call :=
  let Hcrash := fresh "Hcrash" in
  wpc_rec Hcrash;
  [ try iFromCache; crash_case .. |
    try wpc_pure1 Hcrash;
      [try iFromCache; crash_case .. |
       repeat (wpc_pure_no_later wp_pure_filter as Hcrash; []); clear Hcrash] ].

Ltac wpc_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wpc_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wpc_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q1 ?Q2) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wpc_bind_core K)
      | fail 1 "wpc_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => fail "wpc_bind: 'wp', not a 'wpc'"
  | _ => fail "wpc_bind: not a 'wpc'"
  end.

Ltac wpc_bind_seq :=
  lazymatch goal with
  | [ |- envs_entails _ (wpc _ _ _ (App (Lam _ ?e2) ?e1) _ _) ] =>
    wpc_bind e1
  end.

Ltac wpc_frame_seq := wpc_bind_seq; wpc_frame.

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
    | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q ?Qc) =>
      reshape_expr e ltac:(fun K e' =>
        wpc_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) =>
        lazymatch P with
        | wpc _ ?k' ?E1' ?e' _ _ =>
          first [ unify k k' | fail 1 "wpc_apply: cannot apply, k mismatch:" k' "≠" k ];
          first [ unify E1 E1' | fail 1 "wpc_apply: cannot apply E1 mismatch:" E1' "≠" E1 ];
          first [ unify e e' | fail 1 "wpc_apply: cannot apply" P ];
          fail "wpc_apply: cannot apply" P
        | _ => fail "wpc_apply: cannot apply" P "(not a wpc)"
        end
      end
    | _ => fail "wpc_apply: not a 'wpc'"
    end).
Tactic Notation "wpc_apply" open_constr(lem) :=
  wpc_apply_core lem (fun H => iApplyHyp H; (try (iSplit; [ iFromCache | try iNext ]))).

Tactic Notation "wpc_if_destruct" :=
  match goal with
  | |- envs_entails _ (wpc _ _ _ (if: Val $ LitV $ LitBool ?cond then _ else _) _ _) =>
    destruct cond eqn:?;
             repeat match goal with
                    (* TODO: factor out common code with wp_if_destruct *)
                    | [ H: (?x <? ?y)%Z = true |- _ ] => apply Z.ltb_lt in H
                    | [ H: (?x <? ?y)%Z = false |- _ ] => apply Z.ltb_ge in H
                    | [ H: (?x <=? ?y)%Z = true |- _ ] => apply Z.leb_le in H
                    | [ H: (?x <=? ?y)%Z = false |- _ ] => apply Z.leb_gt in H
                    | [ H: bool_decide _ = true |- _ ] => apply bool_decide_eq_true_1 in H
                    | [ H: bool_decide _ = false |- _ ] => apply bool_decide_eq_false_1 in H
                    | [ H: Datatypes.negb _ = true |- _ ] => apply negb_true_iff in H; subst
                    | [ H: Datatypes.negb _ = false |- _ ] => apply negb_false_iff in H; subst
                    end
  end.

Tactic Notation "wpc_loadField" :=
  lazymatch goal with
  | |- envs_entails _ (wpc _ _ _ _ _ _) =>
    wpc_bind (struct.loadF _ _ (Val _));
    lazymatch goal with
    | |- envs_entails ?env (wpc _ _ _
                                (App (Val (struct.loadF ?d ?fname))
                                     (Val (LitV (LitLoc ?l)))) _ _) =>
      match env with
      | _ => wpc_frame_go "" base.Right (@nil ident); [idtac]
      | context[Esnoc _ ?i (l ↦[d :: fname] _)%I] =>
        wpc_frame_go i base.Right [i]; [idtac]
      | _ => fail 1 "wpc_loadField: could not frame automatically"
      end;
      wp_loadField;
      iNamed 1
    | _ => fail 1 "wpc_loadField: could not bind a struct.loadF"
    end
  | _ => fail 1 "wpc_loadField: not a wpc"
  end.
