From New.golang.defn Require Export predeclared.

(* "Exception monad" for modeling function returns.

This is not really a monad (there is no bind), but it implements
short-circuiting evaluation where function returns halt execution of subsequent
parts of the program.

The core primitives are [do: e] and [return: e]. These are composed with [m1;;;
m2] (note triple semicolon; this is not the same as GooseLang sequencing). The
key rules are [do: e1 ;;; m2 == e1;; m2] and [return: e1 ;;; m2 == return: e1];
the latter is the "short-circuiting" needed for function returns to halt
execution. This sequencing is also used for loops, which have other
short-circuiting constructs [loop_op ;;; m2 == loop_op], namely [continue] and
[break]. These also halt execution, and are then consumed by the loop combinator
to decide how to proceed for the next iteration.

A function block is executed with [exception_do m], which strips both [do:] and
[return:]; a function can terminate without having used return. You can think of
[return:] as raising an exception and [exception_do] as catching and unwrapping
that exception.

The implementation of these primitives is very simple. [do: e] is [("#execute",
e)] and [return: e] is [("return", e)]. Sequencing is defined as expected for
the rules above. [exception_do m] is simply [Snd m] to remove the label.

*)

Section defn.

Context `{!ffi_syntax}.

Definition execute_val_def : val := (#"execute", #()).
Program Definition execute_val := sealed @execute_val_def.
Definition execute_val_unseal : execute_val = _ := seal_eq _.

Definition return_val_def (v : val) : val := (#"return", v).
Program Definition return_val := sealed @return_val_def.
Definition return_val_unseal : return_val = _ := seal_eq _.

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
    if: (Fst "s1") =⟨go.string⟩ #"execute" then
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
