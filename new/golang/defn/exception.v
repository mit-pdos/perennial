From New Require Export notation.
From New.golang.defn Require Export typing.
From Perennial Require Import base.

Section defn.

Context `{!ffi_syntax}.

Definition execute_val_def (v : val) : val := (#"execute", v).
Program Definition execute_val := sealed @execute_val_def.
Definition execute_val_unseal : execute_val = _ := seal_eq _.

Definition return_val_def (v : val) : val := (#"return", v).
Program Definition return_val := sealed @return_val_def.
Definition return_val_unseal : return_val = _ := seal_eq _.

(* "Exception" monad *)
(* executing to the end without a return produces a #() to match Go's void
return semantics (named return values are translated as return statements using
do_return as defined below). *)
Local Definition do_execute_def : val :=
  λ: "_v", (#"execute", #())
.

Program Definition do_execute := sealed @do_execute_def.
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
Program Definition exception_seq := sealed @exception_seq_def.
Definition exception_seq_unseal : exception_seq = _ := seal_eq _.

Local Definition do_return_def : val :=
  λ: "v", (#"return", Var "v")
.
Program Definition do_return := sealed @do_return_def.
Definition do_return_unseal : do_return = _ := seal_eq _.

Definition exception_do_def : val :=
  λ: "v", Snd "v"
.
Program Definition exception_do := sealed @exception_do_def.
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
