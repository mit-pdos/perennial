From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext: ffi_syntax}.

(* idiomatic wrappers for loop control flow *)
Definition Continue: val := #true.
Definition Break: val := #false.

Definition For: val :=
  λ: "cond" "body" "post",
  (rec: "loop" <> :=
     let: "continue" :=
        (if: (Var "cond") #()
         then (Var "body") #()
         else #false) in
     if: (Var "continue")
     then (Var "post") #();; (Var "loop") #()
     else #()) #().

Definition Loop: val :=
  λ: "body",
  (rec: "loop" <> :=
     let: "continue" := (Var "body") #() in
     if: Var "continue"
     then (Var "loop") #()
     else #()) #().

End goose_lang.

Notation "'for:' cond ; post := e" := (For cond%E e%E post%E)
  (at level 200, cond, post at level 1, e at level 200,
   format "'[' 'for:'  cond  ;  post  :=  '/  ' e ']'") : expr_scope.

Notation "'for:' := e" := (Loop (LamV BAnon e%E))
  (at level 200, e at level 200,
   format "'[' 'for:'  :=  '/  ' e ']'") : expr_scope.
