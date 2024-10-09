From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang lifting.
From iris.proofmode Require Import coq_tactics.
From New.golang.defn Require Export typing.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Module go_val.

Polymorphic Fixpoint V (t : go_type) : Type :=
  match t with
  | uint64T => w64
  | structT d =>
      (fix Vlist (l : list (string * go_type)) : Type :=
         match l with
         | [] => unit
         | (f, t) :: tl => prod (V t) (Vlist tl)
         end) d
  | _ => False
  end.

(*
Fixpoint proj_def t f {d ft} {Heq : TCSimpl t (structT d)} {Hin : TCSimpl (assocl_lookup f d) (Some ft)}
  (v : V t) : V ft.
Proof.
  rewrite -> TCSimpl_eq in Hin. rewrite -> TCSimpl_eq in Heq.
  destruct d as [|[f' ft'] tl].
  - done.
  - simpl in Hin, v. subst. destruct v.
    destruct (_ =? _)%string.
    + inversion Hin; subst. assumption.
    + eapply proj_def.
      { apply _. }
      { rewrite -Hin. done. }
      { done. }
Defined.
*)

Fixpoint proj_def t f {d ft} {Heq : eq t (structT d)} {Hin : eq (assocl_lookup f d) (Some ft)}
  (v : V t) : V ft.
Proof.
  destruct d as [|[f' ft'] tl].
  - done.
  - simpl in Hin, v. subst. destruct v.
    destruct (_ =? _)%string.
    + inversion Hin; subst. assumption.
    + by eapply proj_def.
Defined.
Program Definition proj := unseal (_:seal (@proj_def)). Obligation 1. by eexists. Qed.
Definition proj_unseal : proj = _ := seal_eq _.
Arguments proj (t f) {d ft Heq Hin} (v).
Notation "v .[ t f ]" := (proj t f v (Heq:=eq_refl) (Hin:=eq_refl)).

Definition S1 := structT [("x", uint64T)].
Definition S2 := [("a", uint64T) ; ("b", uint64T); ("c", S1)].

Module S1.
  Definition t : Type := V S1.
  Definition mk (x : w64) : t := (x, tt).
  Definition x (v : t) : w64 := proj S1 "x" v (Heq:=eq_refl) (Hin:=eq_refl).
  Lemma x_simpl c : x (mk c) = c.
  Proof. rewrite /x proj_unseal. reflexivity. Qed.

  Eval simpl in (x (mk 10)).

  Definition mk (a b : w64 ) (c : ) : V (structT exampleDesc) :=
    (W64 10, (W64 3, ((W64 10, tt), tt)))
  .

Definition mk (a b : w64 ) (c : ) : V (structT exampleDesc) :=
  (W64 10, (W64 3, ((W64 10, tt), tt)))
.

Eval cbn in (proj exampleDesc "a" uint64T eq_refl x).

Fixpoint struct_make d : V (structT d).
Proof.
Qed.

Fixpoint proj2 d f t (Hin : assocl_lookup f d = Some t) (v : V (structT d)) : V t :=
  match d with
  | [] => _
  | (f',t') :: tl => if (String.eqb f f') then
                     let v := (eq_rect _ id v (prod (V t') _)
                                 (eq_refl : V (structT d) = (prod (V t') _))) in
                     let '(h, _) := v in h
                   else proj tl f t _ v
  end.


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
Transparent to_val.

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
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_if_true e1 e2 : PureWp True (if: #true then e1 else e2) e1.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_case_inr v e1 e2 : PureWp True (Case (InjRV v) e1 e2) (e2 v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_case_inl v e1 e2 : PureWp True (Case (InjLV v) e1 e2) (e1 v).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_total_le (v1 v2 : val) : PureWp True (TotalLe v1 v2) #(val_le v1 v2).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Search PureExec.
Print expr.

Opaque to_val.


Context (V : Type).
Context (Heq : V = bool).
Check (λ v : V, eq_rect V id v bool Heq).

Definition convert (V : Type) (Heq : V = bool) (v : V) : bool :=
  eq_rect V id v bool Heq.

PureStep (val → val → option val)

Definition un_op_eval (V : Type) (op : un_op) (v : V) : option val :=
  match V as V0, op with
  | bool, NegOp => Some $ #(negb false)
  | Z, NegOp => Some $ #(negb false)
  | _, _ => None
  end
.
Obligation 1.
intros. rewrite -Heq.
Show Proof.

  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (word.not n)
  | NegOp, LitV (LitInt32 n) => Some $ LitV $ LitInt32 (word.not n)
  | NegOp, LitV (LitByte n) => Some $ LitV $ LitByte (word.not n)
  | UToW64Op, LitV (LitInt v)   => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (uint.Z v))
  | SToW64Op, LitV (LitInt v)   => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (sint.Z v))
  | ToStringOp, LitV (LitByte v) => Some $ LitV $ LitString (u8_to_string v)
  | StringLenOp, LitV (LitString v) => Some $ LitV $ LitInt (W64 (String.length v))
  | IsNoStringOverflowOp, LitV (LitString v) => Some $ LitV $ LitBool (bool_decide ((String.length v) < 2^64))
  | _, _ => None
  end.


Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ #(negb b)
  | NegOp, LitV (LitInt n) => Some $ #(word.not n)
  | NegOp, LitV (LitInt32 n) => Some $ #(word.not n)
  | NegOp, LitV (LitByte n) => Some $ #(word.not n)
  | UToW64Op, LitV (LitInt v)   => Some $ #(W64 (uint.Z v)) LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (uint.Z v))
  | SToW64Op, LitV (LitInt v)   => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (sint.Z v))
  | ToStringOp, LitV (LitByte v) => Some $ LitV $ LitString (u8_to_string v)
  | StringLenOp, LitV (LitString v) => Some $ LitV $ LitInt (W64 (String.length v))
  | IsNoStringOverflowOp, LitV (LitString v) => Some $ LitV $ LitBool (bool_decide ((String.length v) < 2^64))
  | _, _ => None
  end.

(* XXX: does not include β-reduction *)
Fixpoint pure_compute (e : expr) : option expr :=
  match e with
  | Rec f x erec => Some $ Val $ RecV f x erec
  | InjL (Val v) => Some $ Val $ InjLV v
  | InjR (Val v) => Some $ Val $ InjRV v
  | UnOp op (Val v) => un_op_eval op v ≫= (λ v, Some $ Val v)
  | _ => None
  end.

PureExec (un_op_eval op v = Some v') 1 (UnOp op v) v'
End instances.

(** Tactics *)
