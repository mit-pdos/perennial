From Perennial.go_lang Require Import notation struct typing.

Module three.
  Definition S := struct.new ["foo" :: intT; "bar" :: boolT; "baz" :: refT intT].
  Section fields.
    Context {ext:ext_op}.
    Definition foo := structF! S "foo".
    Definition bar := structF! S "bar".
    Definition baz := structF! S "baz".
    Fail Definition quux := structF! S "quux".
  End fields.
End three.

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

  Ltac goal_is_exactly_equal :=
    lazymatch goal with
    | [ |- ?a = ?a ] => reflexivity
    | [ |- ?a = ?b ] => idtac a "is not" b; fail "not an exact match"
    | _ => fail "unexpected goal"
    end.

  Theorem foo_is : three.foo = (λ: "v", Fst (Fst (Var' "v")))%V.
  Proof.
    unfold three.foo.
    goal_is_exactly_equal.
  Qed.

  Theorem bar_is : three.bar = (λ: "v", Fst (Snd (Var' "v")))%V.
  Proof.
    unfold three.bar.
    goal_is_exactly_equal.
  Qed.
End go_lang.
