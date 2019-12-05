From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import atomic.
From Perennial.go_lang Require Export tactics lifting array.
From Perennial.go_lang Require Import notation.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
Lemma tac_twp_expr_eval `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    eapply tac_twp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.

Lemma tac_wp_pure `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ Δ' s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.
Lemma tac_twp_pure `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP e2 @ s; E [{ Φ }]) →
  envs_entails Δ (WP e1 @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ?? ->. rewrite -total_lifting.twp_pure_step //.
Qed.

Lemma tac_wp_value `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
Lemma tac_twp_value `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed.

Ltac wp_expr_simpl := wp_expr_eval simpl.

Ltac wp_value_head :=
  first [eapply tac_wp_value || eapply tac_twp_value].

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
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_twp_pure _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try fast_done                  (* The pure condition for PureExec *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.
Lemma tac_twp_bind `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> -> ->. by apply: twp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wp_allocN Δ Δ' s E j K v (n: u64) Φ :
  (0 < int.val n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (array l (replicate (int.nat n) v))) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_allocN.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.
Lemma tac_twp_allocN Δ s E j K v (n: u64) Φ :
  (0 < int.val n)%Z →
  (∀ l, ∃ Δ',
    envs_app false (Esnoc Enil j (array l (replicate (int.nat n) v))) Δ
    = Some Δ' ∧
    envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ? HΔ.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_allocN.
  rewrite left_id. apply forall_intro=> l.
  destruct (HΔ l) as (Δ'&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.

Lemma tac_wp_alloc Δ Δ' s E j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ Free v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦ Free v)%I) right_id wand_elim_r.
Qed.
Lemma tac_twp_alloc Δ s E j K v Φ :
  (∀ l, ∃ Δ',
    envs_app false (Esnoc Enil j (l ↦ Free v)) Δ = Some Δ' ∧
    envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> HΔ.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_alloc.
  rewrite left_id. apply forall_intro=> l.
  destruct (HΔ l) as (Δ'&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦ Free v)%I) right_id wand_elim_r.
Qed.

Lemma tac_wp_load Δ Δ' s E i K l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} Free v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_load Δ s E i K l q v Φ :
  envs_lookup i Δ = Some (false, l ↦{q} Free v)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ??.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_load.
  rewrite envs_lookup_split //; simpl.
  by apply sep_mono_r, wand_mono.
Qed.

Lemma wp_store s E l v v' :
  {{{ ▷ l ↦ Free v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ Free v }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  unfold Store.
Admitted.
Lemma twp_store s E l v v' :
  [[{ l ↦ Free v' }]] Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ Free v }]].
Proof.
  iIntros (Φ) "Hl HΦ".
  unfold Store.
Admitted.

Lemma tac_wp_store Δ Δ' Δ'' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_store Δ Δ' s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v')) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Store (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first by eapply twp_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cmpxchg Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v2)) Δ' = Some Δ'' →
  vals_compare_safe v v1 →
  (v = v1 →
   envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})) →
  (v ≠ v1 →
   envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???? Hsuc Hfail.
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wp_cmpxchg_suc; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wp_cmpxchg_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.
Lemma tac_twp_cmpxchg Δ Δ' s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v2)) Δ = Some Δ' →
  vals_compare_safe v v1 →
  (v = v1 →
   envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }])) →
  (v ≠ v1 →
   envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ??? Hsuc Hfail.
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -twp_bind. eapply wand_apply.
    { eapply twp_cmpxchg_suc; eauto. }
    rewrite /= {1}envs_simple_replace_sound //; simpl.
    apply sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -twp_bind. eapply wand_apply.
    { eapply twp_cmpxchg_fail; eauto. }
    rewrite /= {1}envs_lookup_split //; simpl.
    apply sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wp_cmpxchg_fail Δ Δ' s E i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} Free v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ?????.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_cmpxchg_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_fail Δ s E i K l q v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦{q} Free v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first exact: twp_cmpxchg_fail.
  rewrite envs_lookup_split //=. by do 2 f_equiv.
Qed.

Lemma tac_wp_cmpxchg_suc Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v2)) Δ' = Some Δ'' →
  v = v1 → vals_compare_safe v v1 →
  envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??????; subst.
  rewrite -wp_bind. eapply wand_apply.
  { eapply wp_cmpxchg_suc; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_suc Δ Δ' s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v2)) Δ = Some Δ' →
  v = v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=>?????; subst.
  rewrite -twp_bind. eapply wand_apply.
  { eapply twp_cmpxchg_suc; eauto. }
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

(*
Lemma tac_wp_faa Δ Δ' Δ'' s E i K l (z1 z2:u64) Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV (LitInt z1))%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt $ Word.wplus z1 z2))) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV (LitInt z1)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV (LitInt z2))) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first exact: (wp_faa _ _ _ z1 z2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_faa Δ Δ' s E i K l z1 z2 Φ :
  envs_lookup i Δ = Some (false, l ↦ LitV z1)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (z1 + z2))) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Val $ LitV z1) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -twp_bind. eapply wand_apply; first exact: (twp_faa _ _ _ z1 z2).
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed. *)
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
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).
Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl).
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

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [iSolveTC
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|iSolveTC
         |finish ()]
    in (process_single ()) || (process_array ())
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [iSolveTC
    |solve_mapsto ()
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg _ _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |try solve_vals_compare_safe
    |intros H1; wp_finish
    |intros H2; wp_finish]
  | |- envs_entails _ (twp ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |try solve_vals_compare_safe
    |intros H1; wp_finish
    |intros H2; wp_finish]
  | _ => fail "wp_cmpxchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_fail" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_fail: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_fail _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [iSolveTC
    |solve_mapsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_fail _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_fail: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_suc" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_suc _ _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_suc _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_suc: not a 'wp'"
  end.

(*
Tactic Notation "wp_faa" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_faa: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_faa _ _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_faa _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |wp_finish]
  | _ => fail "wp_faa: not a 'wp'"
  end. *)
