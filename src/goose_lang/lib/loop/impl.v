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
        (if: "cond" #()
         then "body" #()
         else #false) in
     if: "continue"
     then "post" #();; "loop" #()
     else #()) #().

Definition Loop: val :=
  λ: "body",
  (rec: "loop" <> :=
     let: "continue" := "body" #() in
     if: "continue"
     then "loop" #()
     else #()) #().

End goose_lang.

Notation "'for:' cond ; post := e" := (For cond%E e%E post%E)
  (at level 200, cond, post at level 1, e at level 200,
   format "'[' 'for:'  cond  ;  post  :=  '/  ' e ']'") : expr_scope.

Notation "'for:' := e" := (Loop (LamV BAnon e%E))
  (at level 200, e at level 200,
   format "'[' 'for:'  :=  '/  ' e ']'") : expr_scope.
