From Perennial.goose_lang Require Import
     lang notation struct typing.

Open Scope heap_types.

Module three.
  Section types.
    Context {ext:ext_op} {ext_ty: ext_types ext}.
    Definition S := struct.decl ["foo" :: uint64T; "bar" :: boolT; "baz" :: refT uint64T].
    Definition T := struct.t S.
    Definition foo := structF! S "foo".
    Definition bar := structF! S "bar".
    Definition baz := structF! S "baz".
    Fail Definition quux := structF! S "quux".
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

  Theorem t_is : three.T = (uint64T * boolT * refT uint64T)%ht.
  Proof.
    reflexivity.
  Qed.

  Theorem foo_is : three.foo = (λ: "v", Fst (Fst (Var "v")))%V.
  Proof.
    unfold three.foo.
    goal_is_exactly_equal.
  Qed.

  Theorem bar_is : three.bar = (λ: "v", Snd (Fst (Var "v")))%V.
  Proof.
    unfold three.bar.
    goal_is_exactly_equal.
  Qed.

  Theorem fieldOffset_is l : struct.fieldPointer three.S "bar" l = fieldPointer three.S "bar" l.
  Proof.
    goal_is_exactly_equal.
  Qed.

  Fail Example fieldOffset_check l : fieldOffset three.S "foobar" l = l.

  Theorem foo_t : ⊢ three.foo : (three.T -> uint64T).
  Proof. typecheck. Qed.

  Theorem bar_t : ⊢ three.bar : (three.T -> boolT).
  Proof. typecheck. Qed.

  Theorem baz_t : ⊢ three.baz : (three.T -> refT uint64T).
  Proof. typecheck. Qed.

End goose_lang.
