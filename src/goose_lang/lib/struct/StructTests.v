From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang.lib Require Import struct.impl.

Open Scope heap_types.
Open Scope struct_scope.

Module three.
  Section types.
    Context {ext:ext_op} {ext_ty: ext_types ext}.
    Definition S := struct.decl ["foo" :: uint64T; "bar" :: boolT; "baz" :: refT uint64T].
    Global Instance wf : struct.wf S := _.
  End types.
End three.

Section goose_lang.
  Context `{ext_ty: ext_types}.
  Coercion Var' (s:string) : expr := Var s.

  Ltac goal_is_exactly_equal :=
    lazymatch goal with
    | [ |- ?a = ?a ] => reflexivity
    | [ |- ?a = ?b ] => idtac a "is not" b; fail "not an exact match"
    | _ => fail "unexpected goal"
    end.

  Theorem t_is : struct.t three.S = (uint64T * (boolT * (refT uint64T * unitT)))%ht.
  Proof. reflexivity. Qed.

  Theorem foo_is : getField three.S "foo" = (λ: "v", Fst $ Var "v")%V.
  Proof.
    unfold struct.get; simpl.
    goal_is_exactly_equal.
  Qed.

  Theorem bar_is : getField three.S "bar" = (λ: "v", Fst $ Snd $ Var "v")%V.
  Proof.
    unfold struct.get; simpl.
    goal_is_exactly_equal.
  Qed.

  Theorem foo_t : ⊢ getField three.S "foo" : (struct.t three.S -> uint64T).
  Proof. typecheck. Qed.

  Theorem bar_t : ⊢ getField three.S "bar" : (struct.t three.S -> boolT).
  Proof. typecheck. Qed.

  Theorem baz_t : ⊢ getField three.S "baz" : (struct.t three.S -> refT uint64T).
  Proof. typecheck. Qed.

End goose_lang.
