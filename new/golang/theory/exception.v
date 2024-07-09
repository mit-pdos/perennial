From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export exception.

Ltac tc_search_pure_exec_ctx :=
    match goal with
    | [ |- PureExec _ _ ?e _] => (reshape_expr e ltac:(fun K e' =>
                                                       simpl;
                                                       apply (pure_exec_fill K);
                                                       apply _
                               ))
    end.

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

Global Instance pure_execute_val (v1 : val) (v : val) : WpPureExec True 6 (exception_seq v1 (execute_val v)) (v1 #()).
Proof.
  rewrite exception_seq_unseal execute_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

Global Instance pure_do_execute_val (v : val) : WpPureExec True 2 (do: v) (execute_val v).
Proof.
  rewrite do_execute_unseal execute_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

Global Instance pure_return_val (v1 : val) (v : val) : WpPureExec True 6 (exception_seq v1 (return_val v)) (return_val v).
Proof.
  rewrite exception_seq_unseal return_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

Global Instance pure_do_return_val (v : val) : WpPureExec True 2 (return: v) (return_val v).
Proof.
  rewrite do_return_unseal return_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

Global Instance pure_exception_do_return_v (v : val) : WpPureExec True 2 (exception_do (return_val v)%E) (v).
Proof.
  rewrite exception_do_unseal return_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

Global Instance pure_exception_do_execute_v (v : val) : WpPureExec True 2 (exception_do (execute_val v)%E) (v).
Proof.
  rewrite exception_do_unseal execute_val_unseal. cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.
End pure_execs.
