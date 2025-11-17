From Perennial.program_logic Require Import language.
From Perennial.goose_lang Require Export lang.
From Perennial.Helpers Require Export ByteString.
Set Default Proof Using "Type".

(** Coercions to make programs easier to type. *)
(* integers by default turn into u64 literals

   note that we can't also make W32 a coercion because otherwise we would have
   ambiguous paths between Z and base_lit.
 *)
Coercion W64 : Z >-> w64.
Add Printing Coercion W64.

Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 ≥ e2" := (BinOp LeOp e2%E e1%E) : expr_scope.
Notation "e1 > e2" := (BinOp LtOp e2%E e1%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.
