From Perennial.goose_lang Require Import lang notation new.exception.

Section goose_lang.
Context {ext: ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition do_break : val := λ: "v", (#(str "break"), Var "v").
Definition do_continue : val := λ: "v", (#(str "continue"), Var "v").

Definition break_val : val := (#(str "break"), #()).
Definition continue_val : val := (#(str "continue"), #()).
Definition execute_val (v : val) : val := (#(str "execute"), v).
Definition return_val (v : val) : val := (#(str "return"), v).

Local Definition do_for_def : val :=
  rec: "loop" "cond" "body" "post" :=
   exception_do (
   if: ~(Var "cond") #() then (return: (do: #()))
   else
     let: "b" := "body" #() in
     if: Fst "b" = #(str "break") then (return: (do: #())) else (do: #()) ;;;
     if: (Fst "b" = #(str "continue")) || (Fst $ Var "b" = #(str "execute"))
          then (do: "post" #();;; return: "loop" "cond" "body" "post") else do: #() ;;;
     return: Var "b"
  ).

Program Definition do_for := unseal (_:seal (@do_for_def)). Obligation 1. by eexists. Qed.
Definition do_for_unseal : do_for = _ := seal_eq _.

Definition do_loop_def: val :=
  λ: "body",
  (rec: "loop" <> := exception_do (
     let: "b" := (Var "body") #() in
     if: Fst $ Var "b" = #(str "break") then (return: (do: #())) else (do: #()) ;;;
     if: (Fst $ Var "b" = #(str "continue")) || (Fst $ Var "b" = #(str "execute"))
          then (return: (Var "loop") #()) else do: #() ;;;
     return: Var "b"
  )) #().

Program Definition do_loop := unseal (_:seal (@do_loop_def)). Obligation 1. by eexists. Qed.
Definition do_loop_unseal : do_loop = _ := seal_eq _.

End goose_lang.

Global Notation "break: e" := (do_break e%E)
  (at level 90, e at level 85,
      format "break:  '[' e ']'") : expr_scope.

Global Notation "continue: e" := (do_continue e%E)
  (at level 90, e at level 85,
      format "continue:  '[' e ']'") : expr_scope.

Notation "'for:' cond ; post := e" := (do_for cond%E e%E post%E)
  (at level 200, cond, post at level 1, e at level 200,
   format "'[' 'for:'  cond  ;  post  :=  '/  ' e ']'") : expr_scope.

Notation "'for:' := e" := (do_loop (LamV BAnon e%E))
  (at level 200, e at level 200,
   format "'[' 'for:'  :=  '/  ' e ']'") : expr_scope.
