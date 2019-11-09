From Perennial.go_lang Require Import notation struct.

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

  Definition threeS := struct ["foo"; "bar"; "baz"].

  Definition Foo: val := structF! threeS "foo".
  Definition Bar: val := structF! threeS "bar".
  Fail Definition Quux: val := structF! threeS "quux".

  Ltac goal_is_exactly_equal :=
    lazymatch goal with
    | [ |- ?a = ?a ] => reflexivity
    | [ |- ?a = ?b ] => idtac a "is not" b; fail "not an exact match"
    | _ => fail "unexpected goal"
    end.

  Theorem Foo_is : Foo = (λ: "v", Fst (Fst (Var' "v")))%V.
  Proof.
    unfold Foo.
    goal_is_exactly_equal.
  Qed.

  Theorem Bar_is : Bar = (λ: "v", Fst (Snd (Var' "v")))%V.
  Proof.
    unfold Bar.
    goal_is_exactly_equal.
  Qed.
End go_lang.
