From New.golang.theory Require Export auto.

Section test.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}
  {interface_sem : go.InterfaceSemantics}.

Record foo_t :=
  mk {
      a : w64;
      b : go_string;
    }.
Global Instance settable_foo : Settable foo_t :=
  settable! mk < a; b >.

Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go go.uint64); (go.EmbeddedField "b"%go go.string)].
Definition foo : go.type := go.Named "foo"%go [].
Axiom zero_val_foo : ZeroVal foo_t.
Global Existing Instance zero_val_foo.

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : to_underlying foo = foo_impl;
    foo_zero_val : zero_val foo_t = mk (zero_val _) (zero_val _);
    foo_go_zero_val : go_zero_val foo = #(zero_val foo_t);
    foo_impl_go_zero_val : go_zero_val foo_impl = #(zero_val foo_t);
    #[global] foo_get_a x :: go.IsGoStepPureDet (StructFieldGet foo "a") #x #x.(a);
    #[global] foo_get_b x :: go.IsGoStepPureDet (StructFieldGet foo "b") #x #x.(b);
    #[global] foo_set_a x a' :: go.IsGoStepPureDet (StructFieldSet foo "a") (#x, #a')%V #(x <|a := a'|>);
    #[global] foo_set_b x b' :: go.IsGoStepPureDet (StructFieldSet foo "b") (#x, #b')%V #(x <|b := b'|>);
    #[global] foo_impl_get_a x :: go.IsGoStepPureDet (StructFieldGet foo_impl "a") #x #x.(a);
    #[global] foo_impl_get_b x :: go.IsGoStepPureDet (StructFieldGet foo_impl "b") #x #x.(b);
    #[global] foo_impl_set_a x a' :: go.IsGoStepPureDet (StructFieldSet foo_impl "a") (#x, #a') #(x <|a := a'|>);
    #[global] foo_impl_set_b x b' :: go.IsGoStepPureDet (StructFieldSet foo_impl "b") (#x, #b') #(x <|b := b'|>);
  }.

Program Global Instance typed_pointsto_foo : TypedPointsto foo_t :=
  {| typed_pointsto_def l dq v :=
      ("a" ∷ struct_field_ref foo "a"%go l ↦{dq} v.(a) ∗
       "b" ∷ struct_field_ref foo "b"%go l ↦{dq} v.(b)
      )%I |}.
Final Obligation.
Proof.
simpl. intros. iNamedSuffix 1 "1". iNamedSuffix 1 "2".
destruct v1, v2; simpl.
iCombine "a1 a2" gives %->.
iCombine "b1 b2" gives %->.
done.
Qed.

Context `{!foo_type_assumptions}.

Global Instance into_val_typed_foo  : IntoValTyped foo_t foo.
Proof using H core_sem pre_sem.
  split.
  - iIntros "* _ HΦ".
    rewrite go.alloc_underlying foo_underlying.
    rewrite go.alloc_struct.
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.struct_field_ref_underlying foo_underlying.
    wp_auto.
    wp_apply wp_GoPrealloc. iIntros (l) "_".

    wp_auto.
    case_bool_decide; subst; wp_pures; last (wp_apply wp_AngelicExit).
    iDestruct "l_field" as "?".

    wp_auto. case_bool_decide; subst; wp_pures; last (wp_apply wp_AngelicExit).

    iApply "HΦ". rewrite foo_zero_val. iFrame.
  - iIntros "* Hl HΦ".
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.load_underlying foo_underlying.
    rewrite go.struct_field_ref_underlying foo_underlying.
    rewrite go.load_struct /=.
    iNamed "Hl".

    wp_pures. wp_apply (wp_load with "[$a]"). iIntros "a". wp_pures.

    wp_bind. rewrite foo_impl_go_zero_val.
    wp_pures. wp_apply (wp_load with "[$b]"). iIntros "b". wp_pures.

    destruct v. iApply "HΦ". iFrame.
  - iIntros "* Hl HΦ".
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.store_underlying foo_underlying.
    rewrite go.struct_field_ref_underlying foo_underlying.
    rewrite go.store_struct /=. iNamed "Hl".

    wp_pures. wp_apply (wp_store with "a"). iIntros "a".
    wp_pures. wp_apply (wp_store with "b"). iIntros "b".

    iApply "HΦ". iFrame.
Qed.

Lemma wp_test T V (v : V) :
  {{{ {{{ True }}} #(methods T "Error") #v #() {{{ (s : go_string), RET #s; True }}} }}}
    (let: "i" := #(interface.mk T #v) in
     let: "z" := MethodResolve (go.error) "Error" #() "i" in
     "z" #())
  {{{ (s : go_string), RET #s; True }}}.
Proof.
  iIntros "% #He HΦ". wp_pures.
  rewrite (go.method_interface go.error).
  2:{ rewrite /go.is_interface_type go.to_underlying_not_named //. }
  wp_auto. wp_apply "He" as "% _". by iApply "HΦ".
Qed.

End test.
