From New.golang.defn Require Export typing mem.
From Perennial Require Import base.


Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (mem.load t e%E) : expr_scope.
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (mem.store t e1%E e2%E) : expr_scope.
