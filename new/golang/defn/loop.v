From New Require Export notation.
From New.golang.defn Require Import exception.

Section goose_lang.
Context {ext: ffi_syntax}.

Definition break_val_def : val := (#"break", #()).
Program Definition break_val := unseal (_:seal (@break_val_def)).
Definition break_val_unseal : break_val = _ := seal_eq _.

Definition continue_val_def : val := (#"continue", #()).
Program Definition continue_val := unseal (_:seal (@continue_val_def)).
Definition continue_val_unseal : continue_val = _ := seal_eq _.

Definition do_break_def : val := λ: "v", (#"break", Var "v").
Program Definition do_break := unseal (_:seal (@do_break_def)).
Definition do_break_unseal : do_break = _ := seal_eq _.

Definition do_continue_def : val := λ: "v", (#"continue", Var "v").
Program Definition do_continue := unseal (_:seal (@do_continue_def)).
Definition do_continue_unseal : do_continue = _ := seal_eq _.

Local Definition do_for_def : val :=
  rec: "loop" "cond" "body" "post" :=
   exception_do (
   if: ~(Var "cond") #() then (return: (do: #()))
   else
     let: "b" := "body" #() in
     if: Fst "b" = #"break" then (return: (do: #())) else (do: #()) ;;;
     if: (Fst "b" = #"continue") || (Fst $ Var "b" = #"execute")
          then (do: "post" #();;; return: "loop" "cond" "body" "post") else do: #() ;;;
     return: Var "b"
  ).

Program Definition do_for := unseal (_:seal (@do_for_def)).
Definition do_for_unseal : do_for = _ := seal_eq _.

Definition do_loop_def: val :=
  λ: "body",
  (rec: "loop" <> := exception_do (
     let: "b" := (Var "body") #() in
     if: Fst $ Var "b" = #"break" then (return: (do: #())) else (do: #()) ;;;
     if: (Fst $ Var "b" = #"continue") || (Fst $ Var "b" = #"execute")
          then (return: (Var "loop") #()) else do: #() ;;;
     return: Var "b"
  )) #().

Program Definition do_loop := unseal (_:seal (@do_loop_def)).
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
