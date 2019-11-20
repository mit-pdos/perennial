From Perennial.go_lang Require Import
     lang notation struct typing.

Open Scope heap_types.

Module three.
  Definition S := struct.decl ["foo" :: intT; "bar" :: boolT; "baz" :: refT intT].
  Definition T := struct.t S.
  Section fields.
    Context {ext:ext_op}.
    Definition foo := structF! S "foo".
    Definition bar := structF! S "bar".
    Definition baz := structF! S "baz".
    Fail Definition quux := structF! S "quux".
  End fields.
End three.

Section go_lang.
  Context `{ext_ty: ext_types}.
  Coercion Var' (s:string) : expr := Var s.

  Ltac goal_is_exactly_equal :=
    lazymatch goal with
    | [ |- ?a = ?a ] => reflexivity
    | [ |- ?a = ?b ] => idtac a "is not" b; fail "not an exact match"
    | _ => fail "unexpected goal"
    end.

  Theorem t_is : three.T = (intT * boolT * refT intT)%ht.
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

  Theorem foo_t : ⊢ three.foo : (three.T -> intT).
  Proof. typecheck. Qed.

  Theorem bar_t : ⊢ three.bar : (three.T -> boolT).
  Proof. typecheck. Qed.

  Theorem baz_t : ⊢ three.baz : (three.T -> refT intT).
  Proof. typecheck. Qed.

  Theorem load_ty_is1 : load_ty (intT * intT * intT)%ht "v" 0 =
                       (!("v" +ₗ #0), !("v" +ₗ #1), !("v" +ₗ #2))%E.
  Proof.
    cbv -[U64].
    goal_is_exactly_equal.
  Qed.

  Theorem load_ty_is2 : load_ty (intT * (intT * intT) * intT)%ht "v" 0 =
                       (!("v" +ₗ #0), (!("v" +ₗ #1), !("v" +ₗ #2)), !("v" +ₗ #3))%E.
  Proof.
    cbv -[U64].
    goal_is_exactly_equal.
  Qed.

  Theorem load_field_is1 : loadField three.S "bar" =
                          (λ: "p", !("p" +ₗ #1))%V.
  Proof.
    cbv -[U64].
    reflexivity.
  Qed.

  Theorem load_field_is2 : loadField three.S "baz" =
                          (λ: "p", !("p" +ₗ #2))%V.
  Proof.
    cbv -[U64].
    reflexivity.
  Qed.

End go_lang.
