From Perennial.go_lang Require Import notation struct.

Module three.
  Definition threeS := mkStruct ["foo"; "bar"; "baz"].
  Section fields.
    Context {ext:ext_op}.
    Definition foo := structF! threeS "foo".
    Definition bar := structF! threeS "bar".
    Definition baz := structF! threeS "baz".
    Fail Definition quux := structF! threeS "quux".
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
