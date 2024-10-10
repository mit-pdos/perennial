From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang lifting.
From iris.proofmode Require Import coq_tactics.
From New.golang.theory Require Export typing.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** Classes that are used to tell [wp_pures] about steps it can take. *)
Section classes.

(* FIXME: add later credits *)
Class PureWp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
  φ (e : expr) (e' : expr) :=
  pure_wp_wp : ∀ stk E Φ (H : φ) K,
  ▷ WP (fill K e') @ stk ; E {{ Φ }} -∗ WP (fill K e) @ stk; E {{ Φ }}.

Global Hint Mode PureWp - - - - - - - - ! - : typeclass_instances.

Lemma tac_wp_pure_wp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
      K e1 Δ Δ' s E (e2 : expr) φ Φ :
  PureWp φ e1 e2 →
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hstep ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". by iApply Hstep.
Qed.

(* Now a few lemmas to help establish PureWp in other ways. *)
Lemma pure_wp_val
  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  φ e v' :
  (∀ stk E Φ (H : φ), ▷ Φ v' -∗ WP e @ stk ; E {{ Φ }}) →
  PureWp φ e (Val v').
Proof.
  intros Hval.
  intros ?????. iIntros "Hwp".
  iApply wp_bind. by iApply Hval.
Qed.

Lemma pure_exec_pure_wp n
  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {φ e e'} :
  PureExec φ (S n) e e' → PureWp φ e e'.
Proof.
  intros ??????.
  iIntros "Hk".
  pose proof @pure_exec_fill.
  iApply (lifting.wp_pure_step_later with "[-]"); [done|].
  repeat iModIntro. iIntros "_". iFrame.
Qed.

End classes.

(** Some basic, primitive instances. Adapted to use `IntoVal`. *)
Section instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_injl (v : val) : PureWp True (InjL v) (InjLV v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_injr (v : val) : PureWp True (InjR v) (InjRV v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_snd (v1 v2 : val) : PureWp True (Snd (v1, v2)%V) v2.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_fst (v1 v2 : val) : PureWp True (Fst (v1, v2)%V) v1.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_recc f x erec : PureWp True (rec: f x := erec)%E (rec: f x := erec)%V.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

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

Global Instance wp_total_le (v1 v2 : val) : PureWp True (TotalLe v1 v2) #(val_le v1 v2).
Proof. apply (pure_exec_pure_wp O). rewrite to_val_unseal. solve_pure_exec. Qed.

Global Instance wp_eq `{!IntoVal V} `{!IntoValTyped V t} `{!IntoValTypedComparable V t} (v1 v2 : V) :
  PureWp True (BinOp EqOp #v1 #v2) #(bool_decide (v1 = v2)).
Proof.
  pose proof (conj (to_val_is_comparable v1) (to_val_is_comparable v2)).
  rewrite to_val_unseal in H.
  cut (bin_op_eval EqOp (to_val_def v1) (to_val_def v2) = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { rewrite to_val_unseal. intros. apply (pure_exec_pure_wp O). solve_pure_exec. }
  rewrite /bin_op_eval /bin_op_eval_eq /=.
  rewrite decide_True //.
  destruct (decide (v1 = v2)) eqn:Hx.
  - subst. rewrite !bool_decide_true //.
  - rewrite !bool_decide_false // -to_val_unseal. by intros Heq%to_val_inj.
Qed.

(** Unops *)
(* w64 unops *)
Global Instance wp_neg_w64 (v : w64) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w64 (v : w64) : PureWp True (u_to_w64 #v) #(W64 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w32 (v : w64) : PureWp True (u_to_w32 #v) #(W32 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_u_to_w8 (v : w64) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w64 (v : w64) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w32 (v : w64) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w64_s_to_w8 (v : w64) : PureWp True (s_to_w8 #v) #(W8 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* w32 unops *)
Global Instance wp_neg_w32 (v : w32) : PureWp True (~#v) #(word.not v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w64 (v : w32) : PureWp True (u_to_w64 #v) #(W64 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w32 (v : w32) : PureWp True (u_to_w32 #v) #(W32 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_u_to_w8 (v : w32) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_s_to_w64 (v : w32) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w32_s_to_w32 (v : w32) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
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

Global Instance wp_w8_u_to_w8 (v : w8) : PureWp True (u_to_w8 #v) #(W8 $ uint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_s_to_w64 (v : w8) : PureWp True (s_to_w64 #v) #(W64 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_s_to_w32 (v : w8) : PureWp True (s_to_w32 #v) #(W32 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_s_to_w8 (v : w8) : PureWp True (s_to_w8 #v) #(W8 $ sint.Z v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_w8_to_string (v : w8) : PureWp True (to_string #v) #(u8_to_string v).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* bool unop *)
Global Instance wp_bool_neg (b : bool) : PureWp True (~ #b) #(negb b).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(* string unop *)
Global Instance wp_StringLength (s : string) : PureWp True (StringLength #s) #(W64 $ String.length s).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_IsNoStringOverflow (s : string) : PureWp True (IsNoStringOverflow #s)
                                                       #(bool_decide ((String.length s) < 2^64)).
Proof. rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

(** Binops *)

(* w64 binop instance *)
Global Instance wp_w64_binop op (v1 v2 : w64) (v : w64) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_word op v1 v2 = Some v) (BinOp op #v1 #v2)%E #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec; destruct H as [Hneq Hword].
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /= in H1. Transitions.monad_inv. eauto.
Qed.

Global Instance wp_w32_binop op (v1 v2 : w32) (v : w32) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_word op v1 v2 = Some v) (BinOp op #v1 #v2)%E #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec; destruct H as [Hneq Hword].
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /= in H1. Transitions.monad_inv. eauto.
Qed.

Global Instance wp_w8_binop op (v1 v2 : w8) (v : w8) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_word op v1 v2 = Some v) (BinOp op #v1 #v2)%E #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec; destruct H as [Hneq Hword].
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval Hword decide_False // union_Some_l /= in H1. Transitions.monad_inv. eauto.
Qed.

Global Instance wp_w8_w64_binop op (v1 : w8) (v2 : w64) (v : w8) :
  PureWp (bin_op_eval_shift op v1 (W8 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  rewrite /bin_op_eval_shift /=.
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w8_w32_binop op (v1 : w8) (v2 : w32) (v : w8) :
  PureWp (bin_op_eval_shift op v1 (W8 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w32_w64_binop op (v1 : w32) (v2 : w64) (v : w32) :
  PureWp (bin_op_eval_shift op v1 (W32 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w32_w8_binop op (v1 : w32) (v2 : w8) (v : w32) :
  PureWp (bin_op_eval_shift op v1 (W32 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w64_w8_binop op (v1 : w64) (v2 : w8) (v : w64) :
  PureWp (bin_op_eval_shift op v1 (W64 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

Global Instance wp_w64_w32_binop op (v1 : w64) (v2 : w32) (v : w64) :
  PureWp (bin_op_eval_shift op v1 (W64 (uint.Z v2)) = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  intros H. destruct op; simpl in H; try by exfalso.
  all: revert H; solve_pure_exec; inversion H; subst; done.
Qed.

(* bool binop *)
Global Instance wp_bool_binop op (v1 v2 v : bool) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_bool op v1 v2 = Some v) (BinOp op #v1 #v2) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O).
  case => ?. solve_pure_exec.
  - rewrite /bin_op_eval decide_False // b /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval decide_False // b /= in H0. by Transitions.monad_inv.
Qed.

Global Instance wp_string_binop op (v1 v2 v : string) :
  PureWp (op ≠ EqOp ∧ bin_op_eval_string op v1 v2 = Some v) (BinOp op #v1 #v2) #v.
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

Global Instance wp_StringGet_w64 (s : string) (i : w64) (v : w8) :
  PureWp (string_to_bytes s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

Global Instance wp_StringGet_w32 (s : string) (i : w32) (v : w8) :
  PureWp (string_to_bytes s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

Global Instance wp_StringGet_w8 (s : string) (i : w8) (v : w8) :
  PureWp (string_to_bytes s !! uint.nat i = Some v) (StringGet #s #i) #v.
Proof.
  rewrite to_val_unseal. apply (pure_exec_pure_wp O). solve_pure_exec.
  - rewrite /bin_op_eval /= H /=. Transitions.monad_simpl.
  - rewrite /bin_op_eval /= H /= in H1. Transitions.monad_inv. done.
Qed.

(* TODO: beta *)

End instances.

(** Tactics *)
