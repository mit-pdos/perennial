From Perennial.goose_lang Require Export notation.

(* Q: Can we get by while keeping `do_return` etc. as sealed? *)
(* Q: what about using modules for sealing? A: might make it impossible to
   unfold, which might actually be useful.
  Q: what about using modules for hiding everything except for a few exported
     defns? So the default is to not export, and anything exported has to
     explicitly marked. *)
Section defn.

Context `{ext_ty: ext_types}.
Context `{!ffi_syntax}.
Local Coercion Var' s: expr := Var s.

Definition execute_val_def (v : val) : val := (#(str "execute"), v).
Program Definition execute_val := unseal (_:seal (@execute_val_def)). Obligation 1. by eexists. Qed.
Definition execute_val_unseal : execute_val = _ := seal_eq _.

Definition return_val_def (v : val) : val := (#(str "return"), v).
Program Definition return_val := unseal (_:seal (@return_val_def)). Obligation 1. by eexists. Qed.
Definition return_val_unseal : return_val = _ := seal_eq _.

(* "Exception" monad *)
Local Definition do_execute_def : val :=
  λ: "v", (#(str "execute"), Var "v")
.

Program Definition do_execute := unseal (_:seal (@do_execute_def)). Obligation 1. by eexists. Qed.
Definition do_execute_unseal : do_execute = _ := seal_eq _.

(* Handle "execute" computations by dropping the final value and running the
   next sequential computation. *)
Local Definition exception_seq_def : val :=
  λ: "s2" "s1",
    if: (Fst "s1") = #(str "execute") then
      "s2" #()
    else
      "s1"
.
Program Definition exception_seq := unseal (_:seal (@exception_seq_def)). Obligation 1. by eexists. Qed.
Definition exception_seq_unseal : exception_seq = _ := seal_eq _.

Local Definition do_return_def : val :=
  λ: "v", (#(str "return"), Var "v")
.
Program Definition do_return := unseal (_:seal (@do_return_def)). Obligation 1. by eexists. Qed.
Definition do_return_unseal : do_return = _ := seal_eq _.

Definition exception_do_def : val :=
  λ: "v", Snd "v"
.
Program Definition exception_do := unseal (_:seal (@exception_do_def)). Obligation 1. by eexists. Qed.
Definition exception_do_unseal : exception_do = _ := seal_eq _.

End defn.

Global Notation "e1 ;;; e2" := (exception_seq (Lam BAnon e2%E)%E e1%E)
  (at level 90, e2 at level 200,
      format "'[' e1  ;;;  '//' e2 ']'") : expr_scope.

Global Notation "do: e" := (do_execute e%E)
  (at level 90, e at level 85,
      format "do:  '[' e ']'") : expr_scope.

Global Notation "return: e" := (do_return e%E)
  (at level 90, e at level 85, format "return:  '[' e ']'") : expr_scope.

From Perennial.goose_lang Require Export lifting.
Section pure_execs.
Context `{ffi_sem: ffi_semantics}.

Lemma pure_exec_trans n1 n φ1 φ2 (e1 e2 e3 : goose_lang.expr) :
  (n1 <= n)%nat →
  PureExec φ1 n1 e1 e2 → PureExec φ2 (n - n1) e2 e3
  → PureExec (φ1 ∧ φ2) n e1 e3.
Proof.
  intros.
  intros [? ?].
  replace (n) with (n1 + (n - n1))%nat.
  2:{ lia. }
  eapply nsteps_trans.
  { by apply H0. }
  { by apply H1. }
Qed.

Lemma pure_exec_S n φ1 φ2 (e1 e2 e3 : goose_lang.expr) :
  PureExec φ1 1 e1 e2 → PureExec φ2 n e2 e3
  → PureExec (φ1 ∧ φ2) (S n) e1 e3.
Proof.
  intros.
  eapply pure_exec_trans.
  2:{ done. }
  { lia. }
  replace (S n - 1)%nat with (n) by lia.
  done.
Qed.

Lemma pure_exec_impl φ1 φ2 n (e1 e2 : goose_lang.expr) (H:(φ2 → φ1)) :
  PureExec φ1 n e1 e2 → PureExec (φ2) n e1 e2.
Proof. intros. intros ?. apply H0. by apply H. Qed.

Lemma pure_exec_fill K φ n (e1 e2 : goose_lang.expr) :
  PureExec φ n e1 e2 → PureExec φ n (ectx_language.fill K e1) (ectx_language.fill K e2).
Proof. apply (pure_exec_fill K). Qed.

Ltac solve_pure_exec_ctx :=
    match goal with
    | [ |- PureExec _ _ ?e _] => (reshape_expr e ltac:(fun K e' =>
                                                       simpl;
                                                       apply (pure_exec_fill K);
                                                       apply _
                               ))
    end.

Global Instance pure_execute_val (v1 : val) (v : val) : WpPureExec True 6 (exception_seq v1 (execute_val v)) (v1 #()).
Proof.
  rewrite exception_seq_unseal execute_val_unseal /=.
  rewrite /exception_seq_def /execute_val_def.
  split; first done.
  eapply pure_exec_impl; first shelve.
  eapply pure_exec_S.
  { solve_pure_exec_ctx. }
  eapply pure_exec_S.
  { simpl. solve_pure_exec_ctx. }
  eapply pure_exec_S.
  { simpl. solve_pure_exec_ctx. }
  eapply pure_exec_S.
  { simpl. solve_pure_exec_ctx. }
  eapply pure_exec_S.
  { simpl. solve_pure_exec_ctx. }
  { simpl. solve_pure_exec_ctx. }
  Unshelve. done.
Qed.

Global Instance pure_do_execute_val (v : val) : WpPureExec True some_n (do: v) (execute_val v).
Admitted.

Global Instance pure_return_val (v1 : expr) (v : val) : WpPureExec True some_n (exception_seq v1 (return_val v)) (return_val v).
Admitted.

Global Instance pure_do_return_val (v : val) : WpPureExec True some_n (return: v) (return_val v).
Admitted.

Global Instance pure_exception_do_return_v (v : val) : WpPureExec True some_n (exception_do (return_val v)%E) (v).
Admitted.

Global Instance pure_exception_do_execute_v (v : val) : WpPureExec True some_n (exception_do (execute_val v)%E) (v).
Admitted.
End pure_execs.
