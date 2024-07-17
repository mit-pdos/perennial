From Perennial.goose_lang Require Export proofmode lifting.
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

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* FIXME: PureWp should go expr → expr for this. *)
Lemma wp_list_Match {s E} (l : list val) (handleNil handleCons : val) :
  ∀ Φ,
  WP (match l with
      | nil => (handleNil #())%V
      | cons a l => (handleCons a (list.val l))%V
      end
    ) @ s ; E {{ Φ }} -∗
  WP list.Match (list.val l) handleNil handleCons @ s ; E {{ Φ }}
.
Proof.
  iIntros (?) "Hwp".
  destruct l; rewrite list.val_unseal /list.Match; by wp_pures.
Qed.

End wps.
