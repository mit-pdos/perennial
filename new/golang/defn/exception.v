From New Require Export notation.
From New.golang.defn Require Export typing.

Section defn.

Context `{!ffi_syntax}.

Definition execute_val_def (v : val) : val := (#"execute", v).
Program Definition execute_val := unseal (_:seal (@execute_val_def)). Obligation 1. by eexists. Qed.
Definition execute_val_unseal : execute_val = _ := seal_eq _.

Definition return_val_def (v : val) : val := (#"return", v).
Program Definition return_val := unseal (_:seal (@return_val_def)). Obligation 1. by eexists. Qed.
Definition return_val_unseal : return_val = _ := seal_eq _.

(* "Exception" monad *)
Local Definition do_execute_def : val :=
  λ: "v", (#"execute", Var "v")
.

Program Definition do_execute := unseal (_:seal (@do_execute_def)). Obligation 1. by eexists. Qed.
Definition do_execute_unseal : do_execute = _ := seal_eq _.

(* Handle "execute" computations by dropping the final value and running the
   next sequential computation. *)
Local Definition exception_seq_def : val :=
  λ: "s2" "s1",
    if: (Fst "s1") = #"execute" then
      "s2" #()
    else
      "s1"
.
Program Definition exception_seq := unseal (_:seal (@exception_seq_def)). Obligation 1. by eexists. Qed.
Definition exception_seq_unseal : exception_seq = _ := seal_eq _.

Local Definition do_return_def : val :=
  λ: "v", (#"return", Var "v")
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
