From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export list.
From New.golang.theory Require Import exception.

Section pure_execs.

Context `{ffi_sem: ffi_semantics}.

Global Instance pure_cons (v : val) (l : list val) :
  WpPureExec True 5 (list.Cons v (list.val l)) (list.val (v :: l)).
Proof.
  rewrite list.Cons_unseal list.val_unseal.
  cbv.
  split; first done.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _. constructor. Unshelve. all: done.
Qed.

End pure_execs.
