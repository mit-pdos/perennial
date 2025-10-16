From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang lifting ipersist.
From Perennial.Helpers Require Export ipm Tactics.
From iris.proofmode Require Import coq_tactics.
(* make sure solve_proper comes from stdpp and not Coq *)
From stdpp Require Export tactics.
From New.golang.defn Require Export notation intoval.
From New.golang.theory Require Export typing.
From Perennial Require Export base.
From Ltac2 Require Import Ltac2.
Import Printf.
Set Default Proof Mode "Classic".

(** Classes that are used to tell [wp_pures] about steps it can take. *)
Section classes.

(* FIXME: add later credits *)
Class PureWp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
  φ (e : expr) (e' : expr) :=
  pure_wp_wp : ∀ stk E Φ (H : φ) K,
  ▷ (£ 1 -∗  WP (fill K e') @ stk ; E {{ Φ }}) -∗ WP (fill K e) @ stk; E {{ Φ }}.

Global Hint Mode PureWp - - - - - - - - ! - : typeclass_instances.

Lemma tac_wp_pure_wp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ Δ' s E Φ :
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". iApply Hwp; [done|iIntros "!# _ //"].
Qed.

Lemma tac_wp_pure_wp_later_credit `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ Δ' s E Φ :
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (£ 1 -∗ WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". by iApply Hwp.
Qed.

(* Now a few lemmas to help establish PureWp in other ways. *)
Lemma pure_exec_pure_wp n
  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ} {φ e e'} :
  PureExec φ (S n) e e' → PureWp φ e e'.
Proof.
  intros ??????.
  iIntros "Hk".
  pose proof @pure_exec_fill.
  iApply (lifting.wp_pure_step_later with "[-]"); [done|].
  repeat iModIntro. iIntros "[Hlc _]". by iApply "Hk".
Qed.

Lemma pure_wp_val `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
  φ (e : expr) (v' : val) :
  (∀ stk E Φ (H: φ),
     ▷ (£ 1 -∗  Φ v') -∗ WP e @ stk; E {{ Φ }}) →
  PureWp φ e v'.
Proof.
  intros Hwp.
  red. intros ?????.
  iIntros "HΦ".
  iApply wp_bind; auto.
  iApply Hwp; auto.
Qed.

End classes.

(** Some basic, primitive instances. Adapted to use `IntoVal`. *)
Section instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.

Global Instance wp_injl (v : val) : PureWp True (InjL v) (InjLV v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_injr (v : val) : PureWp True (InjR v) (InjRV v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_snd (v1 v2 : val) : PureWp True (Snd (v1, v2)%V) v2.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_fst (v1 v2 : val) : PureWp True (Fst (v1, v2)%V) v1.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_recc f x erec : PureWp True (rec: f x := erec)%E #(func.mk f x erec).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_pair (v1 v2 : val) : PureWp True (v1, v2)%E (v1, v2)%V.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_if_false e1 e2 : PureWp True (if: #false then e1 else e2) e2.
Proof. apply (pure_exec_pure_wp O). rewrite to_val_unseal. solve_pure_exec. Qed.

Global Instance wp_if_true e1 e2 : PureWp True (if: #true then e1 else e2) e1.
Proof. apply (pure_exec_pure_wp O). rewrite to_val_unseal. solve_pure_exec. Qed.

Global Instance wp_case_inr v e1 e2 : PureWp True (Case (InjRV v) e1 e2) (e2 v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_case_inl v e1 e2 : PureWp True (Case (InjLV v) e1 e2) (e1 v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Definition wp_eq_val (v1 v2 : val) :
  PureWp (is_comparable v1 ∧ is_comparable v2) (BinOp EqOp v1 v2) #(bool_decide (v1 = v2)).
Proof.
  apply (pure_exec_pure_wp O).
  intros Hcomp.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { rewrite to_val_unseal. solve_pure_exec. }
  rewrite /bin_op_eval /bin_op_eval_eq /=.
  rewrite decide_True //.
Qed.

(* FIXME: 
Global Instance wp_eq `{!IntoVal V} `{!IntoValTyped V t} (v1 v2 : V) :
  PureWp (is_comparable_go_type t = true) (BinOp EqOp #v1 #v2) #(bool_decide (v1 = v2)) | 0.
Proof.
  apply (pure_exec_pure_wp O).
  intros Hcomp.
  pose proof (conj (to_val_is_comparable v1 ltac:(done)) (to_val_is_comparable v2 ltac:(done))).
  revert Hcomp.
  rewrite to_val_unseal in H.
  cut (bin_op_eval EqOp (to_val_def v1) (to_val_def v2) = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { rewrite to_val_unseal. intros ?. solve_pure_exec. }
  rewrite /bin_op_eval /bin_op_eval_eq /=.
  rewrite decide_True //.
  destruct (decide (v1 = v2)) eqn:Hx.
  - subst. rewrite !bool_decide_true //.
  - rewrite !bool_decide_false // -to_val_unseal. by intros Heq%to_val_inj.
Qed. *)

(** Unops *)
(* w64 unops *)
Global Instance wp_neg_w64 (v : w64) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w64 (v : w64) : PureWp True (u_to_w64 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (uint.Z v)) with v by word. done.
Qed.

Global Instance wp_w64_u_to_w32 (v : w64) : PureWp True (u_to_w32 #v) #(W32 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w16 (v : w64) : PureWp True (u_to_w16 #v) #(W16 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w8 (v : w64) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w64 (v : w64) : PureWp True (s_to_w64 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (sint.Z v)) with v by word. done.
Qed.

Global Instance wp_w64_s_to_w32 (v : w64) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w16 (v : w64) : PureWp True (s_to_w16 #v) #(W16 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w8 (v : w64) : PureWp True (s_to_w8 #v) #(W8 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* w32 unops *)
Global Instance wp_neg_w32 (v : w32) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w64 (v : w32) : PureWp True (u_to_w64 #v) #(W64 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w32 (v : w32) : PureWp True (u_to_w32 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (uint.Z v)) with v by word. done.
Qed.

Global Instance wp_w32_u_to_w16 (v : w32) : PureWp True (u_to_w16 #v) #(W16 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w8 (v : w32) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_s_to_w64 (v : w32) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_s_to_w32 (v : w32) : PureWp True (s_to_w32 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (sint.Z v)) with v by word. done.
Qed.

Global Instance wp_w32_s_to_w16 (v : w32) : PureWp True (s_to_w16 #v) #(W16 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_s_to_w8 (v : w32) : PureWp True (s_to_w8 #v) #(W8 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* w8 unops *)
Global Instance wp_neg_w8 (v : w8) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_u_to_w64 (v : w8) : PureWp True (u_to_w64 #v) #(W64 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_u_to_w32 (v : w8) : PureWp True (u_to_w32 #v) #(W32 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_u_to_w8 (v : w8) : PureWp True (u_to_w8 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (uint.Z v)) with v by word. done.
Qed.

Global Instance wp_w8_s_to_w64 (v : w8) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_s_to_w32 (v : w8) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_s_to_w8 (v : w8) : PureWp True (s_to_w8 #v) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  solve_pure_exec. replace (_ (sint.Z v)) with v by word. done.
Qed.

Global Instance wp_w8_to_string (v : w8) : PureWp True (to_string #v) #([v]).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* w16 unops *)
Global Instance wp_neg_w16 (v : w16) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_u_to_w64 (v : w16) : PureWp True (u_to_w64 #v) #(W64 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_u_to_w32 (v : w16) : PureWp True (u_to_w32 #v) #(W32 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_u_to_w16 (v : w16) : PureWp True (u_to_w16 #v) #(W16 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_u_to_w8 (v : w16) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_s_to_w64 (v : w16) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_s_to_w32 (v : w16) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_s_to_w16 (v : w16) : PureWp True (s_to_w16 #v) #(W16 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w16_s_to_w8 (v : w16) : PureWp True (s_to_w8 #v) #(W8 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* bool unop *)
Global Instance wp_bool_neg (b : bool) : PureWp True (~ #b) #(negb b).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* string unop *)
Global Instance wp_StringLength (s : go_string) : PureWp True (StringLength #s) #(W64 $ length s).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_IsNoStringOverflow (s : go_string) : PureWp True (IsNoStringOverflow #s)
                                                       #(bool_decide ((length s) < 2^64)).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(** Binops *)

(* w64 binop instance *)
Global Instance wp_w64_binop op (v1 v2 : w64) (v : val) :
  PureWp (op ≠ EqOp ∧
      (to_val <$> bin_op_eval_word op v1 v2) ∪ (to_val <$> bin_op_eval_compare op v1 v2) = Some v)
    (BinOp op #v1 #v2)%E v | 1.
Proof.
  rewrite to_val_unseal /=. apply (pure_exec_pure_wp O).
  intros [??]. assert (bin_op_eval op (LitV v1) (LitV v2) = Some v).
  { rewrite /bin_op_eval decide_False // /=. destruct op; try by simpl in *. }
  revert H. solve_pure_exec.
Qed.

Global Instance wp_w32_binop op (v1 v2 : w32) (v : val) :
  PureWp (op ≠ EqOp ∧
      (to_val <$> bin_op_eval_word op v1 v2) ∪ (to_val <$> bin_op_eval_compare op v1 v2) = Some v)
    (BinOp op #v1 #v2)%E v | 1.
Proof.
  rewrite to_val_unseal /=. apply (pure_exec_pure_wp O).
  intros [??]. assert (bin_op_eval op (LitV v1) (LitV v2) = Some v).
  { rewrite /bin_op_eval decide_False // /=. destruct op; try by simpl in *. }
  revert H. solve_pure_exec.
Qed.

Global Instance wp_w16_binop op (v1 v2 : w16) (v : val) :
  PureWp (op ≠ EqOp ∧
      (to_val <$> bin_op_eval_word op v1 v2) ∪ (to_val <$> bin_op_eval_compare op v1 v2) = Some v)
    (BinOp op #v1 #v2)%E v | 1.
Proof.
  rewrite to_val_unseal /=. apply (pure_exec_pure_wp O).
  intros [??]. assert (bin_op_eval op (LitV v1) (LitV v2) = Some v).
  { rewrite /bin_op_eval decide_False // /=. destruct op; try by simpl in *. }
  revert H. solve_pure_exec.
Qed.

Global Instance wp_w8_binop op (v1 v2 : w8) (v : val) :
  PureWp (op ≠ EqOp ∧
      (to_val <$> bin_op_eval_word op v1 v2) ∪ (to_val <$> bin_op_eval_compare op v1 v2) = Some v)
    (BinOp op #v1 #v2)%E v | 1.
Proof.
  rewrite to_val_unseal /=. apply (pure_exec_pure_wp O).
  intros [??]. assert (bin_op_eval op (LitV v1) (LitV v2) = Some v).
  { rewrite /bin_op_eval decide_False // /=. destruct op; try by simpl in *. }
  revert H. solve_pure_exec.
Qed.

Global Instance wp_w8_w64_binop op (v1 : w8) (v2 : w64) (v : w8) :
  PureWp (bin_op_eval_shift op v1 (W8 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  rewrite /bin_op_eval_shift /=.
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w8_w16_binop op (v1 : w8) (v2 : w16) (v : w8) :
  PureWp (bin_op_eval_shift op v1 (W8 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w8_w32_binop op (v1 : w8) (v2 : w32) (v : w8) :
  PureWp (bin_op_eval_shift op v1 (W8 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w32_w64_binop op (v1 : w32) (v2 : w64) (v : w32) :
  PureWp (bin_op_eval_shift op v1 (W32 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w32_w16_binop op (v1 : w32) (v2 : w16) (v : w32) :
  PureWp (bin_op_eval_shift op v1 (W32 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w32_w8_binop op (v1 : w32) (v2 : w8) (v : w32) :
  PureWp (bin_op_eval_shift op v1 (W32 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w64_w16_binop op (v1 : w64) (v2 : w16) (v : w64) :
  PureWp (bin_op_eval_shift op v1 (W64 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w64_w8_binop op (v1 : w64) (v2 : w8) (v : w64) :
  PureWp (bin_op_eval_shift op v1 (W64 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w64_w32_binop op (v1 : w64) (v2 : w32) (v : w64) :
  PureWp (bin_op_eval_shift op v1 (W64 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w16_w64_binop op (v1 : w16) (v2 : w64) (v : w16) :
  PureWp (bin_op_eval_shift op v1 (W16 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w16_w32_binop op (v1 : w16) (v2 : w32) (v : w16) :
  PureWp (bin_op_eval_shift op v1 (W16 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w16_w8_binop op (v1 : w16) (v2 : w8) (v : w16) :
  PureWp (bin_op_eval_shift op v1 (W16 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

(* bool binop *)
Global Instance wp_bool_binop op (v1 v2 v : bool) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_bool op v1 v2 = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  case => ?. solve_pure_exec.
  - rewrite /bin_op_eval decide_False // b /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval decide_False // b /= in H0. by Transitions.monad_inv.
Qed.

Global Instance wp_string_binop op (v1 v2 v : go_string) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_string op v1 v2 = Some v) (BinOp op #v1 #v2) #v | 1.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  case => ?. solve_pure_exec.
  - rewrite /bin_op_eval decide_False // b /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval decide_False // b /= in H0. by Transitions.monad_inv.
Qed.

Global Instance wp_offset k (l : loc) (off : w64) :
  PureWp True (BinOp (OffsetOp k) #l #off) #(l +ₗ k * (uint.Z off)).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* string lookup ops *)

Global Instance wp_StringGet_w64 (s : go_string) (i : w64) (v : w8) :
  PureWp (s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

Global Instance wp_StringGet_w32 (s : go_string) (i : w32) (v : w8) :
  PureWp (s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

Global Instance wp_StringGet_w16 (s : go_string) (i : w16) (v : w8) :
  PureWp (s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

Global Instance wp_StringGet_w8 (s : go_string) (i : w8) (v : w8) :
  PureWp (s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

(* XXX: making this an instance results in this fact getting used even in places
  where the RecV is under a definition. Making it an explicit [Hint Extern]
  below alleviates this problem, and only applies [wp_call] when the goal
  expression is syntactically a [RecV]. *)
Definition wp_call (v2 : val) f x e :
  PureWp True (App (rec: f x := e)%V v2) (subst' x v2 (subst' f (rec: f x := e)%V e)).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_call_go_func (v2 : val) f x e :
  PureWp True (App #(func.mk f x e) v2) (subst' x v2 (subst' f #(func.mk f x e) e)).
Proof. rewrite to_val_unseal /=. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

End instances.

Global Hint Extern 0 (PureWp _ (App (Val (RecV _ _ _)) _) _) => simple apply wp_call : typeclass_instances.

Section lemmas.
Lemma tac_wp_bind `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseLocalGS Σ, !gooseGlobalGS Σ}
    K e Δ s E Φ f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that the `wp_bind`
                           tactic can `simpl` the RHS to get a concrete function
                           f which results in a nice looking output without
                           `fill K` appearing. *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Lemma tac_wp_rec `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      K v1 v2 {f x e} {Hwp:TCEq v1 (rec: f x := e)%V} Δ Δ' s E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (£ 1 -∗ WP (fill K (subst' x v2 (subst' f v1 e))) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K (App v1 v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". rewrite TCEq_eq in Hwp. rewrite Hwp.
  by iApply wp_call.
Qed.

Lemma tac_wp_call_go_func `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      K f x e v2 Δ Δ' s E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K (subst' x v2 (subst' f #(func.mk f x e) e))) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K (#(func.mk f x e) v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". iApply wp_call_go_func; [done|iIntros "!# _ //"].
Qed.

End lemmas.

(** Tactics *)

Ltac2 Type exn ::= [ Walk_expr_more ].
Ltac2 Type exn ::= [ Walk_expr_not_found ].

Ltac2 walk_expr (e : constr) (f : constr -> constr -> 'a) : 'a :=
  let rec walk_ctx (e : constr) (k : constr) :=
    lazy_match! e with | Val _ => Control.zero Walk_expr_not_found | _ => () end;
    match Control.case (fun () => f e k) with
    | Val (a, _) => a
    | Err Walk_expr_more =>
        lazy_match! e with
        | fill ?k' ?e                     => walk_ctx e constr:($k ++ $k')
        | App ?e1 (Val ?v)                => walk_ctx e1 constr:(@AppLCtx _ $v :: $k)
        | App ?e1 ?e2                     => walk_ctx e2 constr:(@AppRCtx _ $e1 :: $k)
        | UnOp ?op ?e                     => walk_ctx e constr:(@UnOpCtx _ $op :: $k)
        | BinOp ?op (Val ?v) ?e           => walk_ctx e constr:(@BinOpRCtx _ $op $v :: $k)
        | BinOp ?op ?e1 ?e2               => walk_ctx e1 constr:(@BinOpLCtx _ $op $e2 :: $k)
        | If ?e0 ?e1 ?e2                  => walk_ctx e0 constr:(IfCtx $e1 $e2 :: $k)
        | Pair (Val ?v) ?e                => walk_ctx e constr:(PairRCtx $v :: $k)
        | Pair ?e1 ?e2                    => walk_ctx e1 constr:(PairLCtx $e2 :: $k)
        | Fst ?e                          => walk_ctx e constr:(@FstCtx _ :: $k)
        | Snd ?e                          => walk_ctx e constr:(@SndCtx _ :: $k)
        | InjL ?e                         => walk_ctx e constr:(@InjLCtx _ :: $k)
        | InjR ?e                         => walk_ctx e constr:(@InjRCtx _ :: $k)
        | Case ?e0 ?e1 ?e2                => walk_ctx e0 constr:(CaseCtx $e1 $e2 :: $k)
        | Primitive2 ?op (Val ?v) ?e      => walk_ctx e constr:(@Primitive2RCtx _ $op $v :: $k)
        | Primitive2 ?op ?e1 ?e2          => walk_ctx e1 constr:(@Primitive2LCtx _ $op $e2 :: $k)
        | Primitive1 ?op ?e               => walk_ctx e constr:(@Primitive1Ctx _ $op :: $k)
        | @ExternalOp ?ext ?op ?e         => walk_ctx e constr:(@ExternalOpCtx $ext $op :: $k)
        | CmpXchg (Val ?v0) (Val ?v1) ?e2 => walk_ctx e2 constr:(CmpXchgRCtx $v0 $v1 :: $k)
        | CmpXchg (Val ?v0) ?e1 ?e2       => walk_ctx e1 constr:(CmpXchgMCtx $v0 $e2 :: $k)
        | CmpXchg ?e0 ?e1 ?e2             => walk_ctx e0 constr:(CmpXchgLCtx $e1 $e2 :: $k)
        | ResolveProph (Val ?v) ?e        => walk_ctx e constr:(@ResolveProphRCtx _ $v :: $k)
        | ResolveProph ?e1 ?e2            => walk_ctx e1 constr:(@ResolveProphLCtx _ $e2 :: $k)
        | Rec _ _ _ => Control.zero Walk_expr_not_found
        | Fork _ => Control.zero Walk_expr_not_found
        | Primitive0 _ => Control.zero Walk_expr_not_found
        | _ => Control.zero (Tactic_failure (Some (fprintf "walk_expr: no match for expr %t" e)))
        end
    | Err e => Control.zero e
    end
  in (walk_ctx e) constr:(@nil ectx_item).

Ltac2 wp_walk_unwrap t s :=
  match Control.case t with
  | Val (a, _) => a
  | Err Walk_expr_not_found => Control.backtrack_tactic_failure s
  | Err e => Control.zero e
  end
.

(* Maybe avoid MaybeIntoLaterNEnvs if there are no  laters syntactically. *)
Ltac2 wp_pure_visit e k :=
     (* This looks for an instance before eapply to make to fail fast. *)
     let pure_wp := orelse (fun () => '(ltac:(tc_solve) : PureWp _ $e _))
                      (fun _ => Control.zero Walk_expr_more) in
     eapply (tac_wp_pure_wp $k $e $pure_wp) >
       [ltac1:(try done)|
         ltac1:(tc_solve)|
         ltac1:(reduction.pm_prettify; simpl subst'; simpl fill)].

Ltac2 wp_pure () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ (Val _) _) ] => ltac1:(iApply wp_value)
  | [ |- envs_entails _ (wp _ _ ?e _) ] =>
      wp_walk_unwrap
        (fun () => walk_expr e wp_pure_visit)
        "wp_pure: could not find a head subexpression with a known next step"
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_pure: current proof is not a WP"
  end.

Ltac2 wp_pure_lc_visit e k :=
  (* This looks for an instance before eapply to make to fail fast. *)
  let pure_wp := orelse (fun () => '(ltac:(tc_solve) : PureWp _ $e _))
                   (fun _ => Control.zero Walk_expr_more) in
  eapply (tac_wp_pure_wp_later_credit $k $e $pure_wp) >
    [ltac1:(try done)|
      ltac1:(tc_solve)|
      ltac1:(reduction.pm_prettify; simpl subst';
             simpl fill)].

Ltac2 wp_pure_lc () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ (Val _) _) ] => ltac1:(iApply wp_value)
  | [ |- envs_entails _ (wp _ _ ?e _) ] =>
      wp_walk_unwrap (fun () => walk_expr e wp_pure_lc_visit)
        "wp_pure: could not find a head subexpression with a known next step"
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_pure: current proof is not a WP"
  end.
Tactic Notation "wp_pure" := ltac2:(Control.enter wp_pure).
Tactic Notation "wp_pure_lc" constr(H) := ltac2:(Control.enter wp_pure_lc); iIntros H.
Tactic Notation "wp_pures" := repeat (wp_pure; []).

Ltac2 wp_call_visit e k :=
  orelse (fun () => Std.unify e '(App (rec: _ _ := _)%V _))
    (fun _ => Control.zero Walk_expr_more);
  eapply (tac_wp_rec $k) >
    [ltac1:(tc_solve) | ltac1:(tc_solve)|
      ltac1:(reduction.pm_prettify; simpl subst'; simpl fill)].

Ltac2 wp_call () :=
  (* XXX: this is when `zero_val`s tend to show up (unfolding the body of a
     function), so try rewriting to use IntoValTyped's default. *)
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      wp_walk_unwrap (fun () => walk_expr e wp_call_visit)
        "wp_call: could not find a function call expression at the head"
      (* try (rewrite <- !default_val_eq_zero_val) *)
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_call: current proof is not a WP"
  end.
Tactic Notation "wp_call" := ltac2:(Control.enter wp_call); iIntros "_"; wp_pures.
Tactic Notation "wp_call_lc" constr(H) := ltac2:(Control.enter wp_call); iIntros H; wp_pures.

Ltac pure_wp_start :=
  apply pure_wp_val; intros ????;
  iIntros "HΦ"; try (wp_call_lc "Hlc"; try iSpecialize ("HΦ" with "[$Hlc]")).

Ltac2 wp_bind_filter (filter_tac : constr -> unit) : constr :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      orelse (fun () => filter_tac e; e) (* if the top-level matches, don't walk down the expr at all. *)
        (fun _ => walk_expr e (fun e' k =>
                              orelse (fun () => filter_tac e')
                                (fun _ => Control.zero Walk_expr_more);
                              eapply (tac_wp_bind $k $e') >
                                [simpl; reflexivity|ltac1:(reduction.pm_prettify)]; e'))
  end.

Tactic Notation "wp_bind" open_constr(e) :=
  let f := ltac2:(e |-
                    let e := Ltac1.to_constr e in
                    let e := Option.get e in
                    orelse
                      (fun () => let _ := wp_bind_filter (Std.unify e) in ())
                      (fun _ => Control.backtrack_tactic_failure "wp_bind: could not find pattern")
                 ) in
  f e.

Ltac2 wp_bind_next () : unit :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      let bind_ctx := Ref.ref None in
      let is_call_so_far := Ref.ref true in
      match Control.case (
                fun () => walk_expr e
                         (fun e k => lazy_match! e with
                                  | App _ (Val _) => (if (Ref.get is_call_so_far) then ()
                                                     else Ref.set bind_ctx (Some (e,k)));
                                                    Ref.set is_call_so_far true
                                  | _ => Ref.set bind_ctx (Some (e,k));
                                        Ref.set is_call_so_far false
                                  end; Control.zero Walk_expr_more)) with
      | Err Walk_expr_not_found => ()
      | Err e => Control.zero e
      | _ => Control.throw (Tactic_failure (Some (fprintf "wp_bind_next: expected walk_expr to raise an exception")))
      end;
      match (Ref.get bind_ctx) with
      | None => ()
      | Some (e, k) =>
          lazy_match! k with
          | nil => ()
          | _ => eapply (tac_wp_bind $k $e) > [simpl; reflexivity|ltac1:(reduction.pm_prettify)]
          end
      end
  end.

Tactic Notation "wp_bind" := ltac2:(wp_bind_next ()).

Lemma tac_wp_true_elim Σ Δ (P: iProp Σ) :
  envs_entails Δ P ->
  envs_entails Δ (bi_wand (bi_pure True) P).
Proof. rewrite envs_entails_unseal=> ->. iIntros "$ _ //". Qed.

Lemma tac_wp_true Σ (Δ: envs (iPropI Σ)) :
  envs_entails Δ (bi_pure True).
Proof. done. Qed.

Ltac2 solve_bi_true () :=
  lazy_match! goal with
  | [ |- envs_entails _ (bi_pure True) ] => apply tac_wp_true
  | [ |- envs_entails _ (bi_wand (bi_pure True) _) ] => apply tac_wp_true_elim
  end.

Tactic Notation "wp_apply_core" open_constr(lem) :=
  ltac2:(Control.enter wp_bind_next);
  iApply lem; try iNext; try ltac2:(Control.enter solve_bi_true).

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem.


Section go_wp_pure_instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.

Global Instance wp_GoLoad t (l : loc) :
  PureWp True (GoInstruction (GoLoad t) #l) (load t #l).
Proof.
  iIntros "% * _ % HΦ". rewrite to_val_unseal. iApply wp_GoLoad. iApply "HΦ".
Qed.


Global Instance wp_StructFieldRef t f (l : loc) :
  PureWp True (GoInstruction (StructFieldRef t f) #l) #(struct_field_ref t f l).
Proof.
  iIntros "% * _ % HΦ". wp_bind.
  rewrite to_val_unseal. iApply wp_StructFieldRef. iApply "HΦ".
Qed.

End go_wp_pure_instances.

Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  `{!NamedUnderlyingTypes} `{!go.MemOps}.

Lemma wp_untyped_load l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    ! #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof. rewrite to_val_unseal. apply lifting.wp_load. Qed.

Program Global Instance into_val_proof_loc : IntoValProof loc :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Existing Class go.is_primitive.
Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.

Program Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Next Obligation.
  iIntros "* Hl HΦ".
  rewrite go.load_primitive.
  wp_pures. rewrite typed_pointsto_unseal /=.
  wp_apply (wp_untyped_load with "Hl").
  iIntros "Hl". by iApply "HΦ".
Qed.

Local Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  rewrite go.load_primitive;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (wp_untyped_load with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Final Obligation.
Admitted.

Local Ltac solve_wp_store := admit.

Program Global Instance into_val_inj_w64 : IntoValProof w64 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w64 : IntoValTyped w64 go.uint64.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_inj_w32 : IntoValProof w32 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w32 : IntoValTyped w32 go.uint32.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_inj_w16 : IntoValProof w16 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w16 : IntoValTyped w16 go.uint16.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_inj_w8 : IntoValProof w8 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w8 : IntoValTyped w8 go.uint8.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_inj_bool : IntoValProof bool :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_bool : IntoValTyped bool go.bool.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_inj_string : IntoValProof go_string :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_string : IntoValTyped go_string go.string.
Next Obligation. solve_wp_load. Qed.
Next Obligation. solve_wp_store. Admitted.

Program Global Instance into_val_typed_slice : IntoValTyped slice.t sliceT :=
{| default_val := slice.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal. move => [???][???] [=].
                 repeat intros [=->%to_val_inj]. done.
Qed.

(* Using [vec] here because the [to_val] must be a total function that always
   meets [has_go_type]. An alternative could be a sigma type. *)
Program Global Instance into_val_typed_array `{!IntoVal V} `{!IntoValTyped V t} n :
  IntoValTyped (vec V n) (arrayT n t) :=
{| default_val := vreplicate n (default_val _) |}.
Next Obligation.
  rewrite to_val_unseal /=.
  solve_has_go_type.
  induction v as [|].
  - apply (has_go_type_array 0 t []); done.
  - simpl in *.
    inversion IHv. subst.
    pose proof (has_go_type_array (S (length a)) t (#h::a) ltac:(done)) as Ht.
    simpl in Ht. apply Ht. intros ? [|].
    + subst. apply to_val_has_go_type.
    + apply Helems. done.
Qed.
Next Obligation.
  intros.
  rewrite to_val_unseal zero_val_eq /=.
  rewrite -zero_val_unseal -default_val_eq_zero_val.
  induction n; first done. simpl. f_equal. apply IHn.
Qed.
Final Obligation.
rewrite to_val_unseal.
intros. intros ?? Heq.
simpl in Heq.
induction x.
{ rewrite (VectorSpec.nil_spec y) //. }
destruct y using vec_S_inv.
simpl in *.
injection Heq as Heq1 Heq.
apply to_val_inj in Heq1. subst.
f_equal. by apply IHx.
Qed.

Program Global Instance into_val_typed_func : IntoValTyped func.t funcT :=
{| default_val := func.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => [[???] [???]] /= [=] //. naive_solver.
Qed.
Final Obligation. solve_decision. Qed.

Program Global Instance into_val_typed_interface : IntoValTyped interface.t interfaceT :=
{| default_val := interface.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation.
  rewrite to_val_unseal => [x y] Heq.
  destruct x as [|], y as [|].
  {
    simpl in *.
    injection Heq as Heq1 Heq2.
    apply to_val_inj in Heq1. subst. done.
  }
  all: first [discriminate | reflexivity].
Qed.
Final Obligation.
  solve_decision.
Qed.

Program Global Instance into_val_typed_unit : IntoValTyped unit (structT []) :=
{| default_val := tt |}.
Next Obligation.
  intros [].
  replace (#()) with (struct.val_aux (structT []) []).
  2:{ rewrite struct.val_aux_unseal //. }
  by constructor.
Qed.
Next Obligation. rewrite zero_val_eq /= struct.val_aux_unseal //. Qed.
Final Obligation.
  intros ???. destruct x, y. done.
Qed. *)

End into_val_instances.


Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!NamedUnderlyingTypes}.

Context `{!go.MemOps}.
Program Global Instance into_val_typed_uint64 : IntoValTyped loc go.uint64.
Next Obligation.
  iIntros "* Hl HΦ".
  rewrite go.load_primitive; [|constructor].
  wp_pures.
Admitted.
Final Obligation. Admitted.

Program Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Next Obligation.
  iIntros "* Hl HΦ".
  rewrite go.load_primitive; [|constructor].
  wp_pures.
Admitted.
Final Obligation. Admitted.

Record foo_t := 
  mk {
      a : w64;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {| to_val_def := λ v, (#v.(a), #())%V; zero_val := (mk (zero_val _)) |}.

Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go go.uint64)].
Definition foo : go.type := go.Named "foo"%go [].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : named_to_underlying "foo"%go [] = foo_impl
  }.

Context `{!foo_type_assumptions}.

(* TODO: struct field_ref. One option is to have field_ref_f be a totally opaque
   function.  All that really matters is it's a deterministic computation and
   that it agrees with allocation.
   E.g. it really doesn't matter if struct fields are packed or not, nor if
   they're in the same order as source code.
 *)
(* TODO: for struct values, what about using a gmap rather than list val?
   Induction principle might be screwed up. *)

Program Global Instance into_val_proof_w64 : IntoValProof w64 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_foo_inj : IntoValProof foo_t :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := (struct_field_ref foo "a"%go l ↦{dq} v.(a))%I |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Admitted.
Next Obligation. solve_decision. Qed.

Lemma foo_split l dq (v : foo_t) :
  l ↦{dq} v ⊢ (struct_field_ref foo "a"%go l) ↦{dq} v.(a).
Proof. done. Qed.

Program Global Instance into_val_typed_foo  : IntoValTyped foo_t foo.
Next Obligation. 
  iIntros "* Hl HΦ".
  iEval (rewrite go.load_underlying /= foo_underlying go.load_struct /=).
  wp_pures. wp_bind.
  iDestruct (foo_split with "Hl") as "Hl".
  Opaque typed_pointsto. (* FIXME: seal typed_pointsto *)
  iEval (rewrite go.struct_field_ref_underlying /= foo_underlying /foo_impl) in "Hl".
  wp_apply (wp_load (t:=go.uint64) with "Hl").
  iIntros "Hl".
  wp_pures.
  (* FIXME: construct StructVal. Have pure op to insert into struct val. Can
     start from empty struct val. Can give list-like notation. *)
Admitted.

(* TODO: Maybe aggregate all the built-in dynamic functions into one instruction? *)

Context `{!GoContext}.
Context `{!MemOps}.

Record foo_t := 
  mk {
      a : w64;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {| to_val_def := λ v, (#v.(a), #())%V; zero_val := (mk (zero_val _)) |}.

Definition foo : go.type := go.Named "foo"%go [].
Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go uint64)].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : named_to_underlying "foo"%go [] = foo_impl
  }.

Context `{!foo_type_assumptions}.

Goal goose_lang.size (go.ArrayType 3 foo) = 3.
  rewrite size_array size_underlying /= foo_underlying
    size_struct /= size_primitive //. constructor.
Qed.

Goal load (go.ArrayType 3 foo) = (λ: "l", ! "l")%V.
  rewrite is_load_array /=. vm_compute Z.add.
  rewrite is_load_underlying /= foo_underlying.
  rewrite is_load_struct /=.
