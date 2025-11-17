From New.golang.defn Require Export predeclared.
From New.golang.theory Require Export postlifting.

Module error.
  Section def.
  Context `{ffi_syntax}.
  Definition t := interface.t.
  End def.
End error.

Section into_val_typed_instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}.

Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite go.alloc_predeclared typed_pointsto_unseal /= into_val_unseal;
  wp_pures; by wp_apply wp_alloc_untyped.

Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  rewrite go.load_predeclared;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_load with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_wp_store :=
  iIntros "* Hl HΦ";
  rewrite go.store_predeclared;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_store with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_into_val_typed := constructor; [solve_wp_alloc|solve_wp_load|solve_wp_store].

Existing Class go.is_predeclared.
#[local] Hint Extern 1 (go.is_predeclared ?t) => constructor : typeclass_instances.
Existing Class go.is_predeclared_zero_val.
#[local] Hint Extern 1 (go.is_predeclared_zero_val ?t ?v) => constructor : typeclass_instances.

Local Set Default Proof Using "Type core_sem pre_sem".
Global Instance into_val_typed_uint64 : IntoValTyped w64 go.uint64.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_uint64 : IntoValComparable w64 go.uint64.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_uint32 : IntoValTyped w32 go.uint32.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_uint32 : IntoValComparable w32 go.uint32.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_uint16 : IntoValTyped w16 go.uint16.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_uint16 : IntoValComparable w16 go.uint16.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_uint8 : IntoValTyped w8 go.uint8.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_uint8 : IntoValComparable w8 go.uint8.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_uint : IntoValTyped w64 go.uint.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_uint : IntoValComparable w64 go.uint.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_int64 : IntoValTyped w64 go.int64.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_int64 : IntoValComparable w64 go.int64.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_int32 : IntoValTyped w32 go.int32.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_int32 : IntoValComparable w32 go.int32.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_int16 : IntoValTyped w16 go.int16.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_int16 : IntoValComparable w16 go.int16.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_int8 : IntoValTyped w8 go.int8.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_int8 : IntoValComparable w8 go.int8.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_int : IntoValTyped w64 go.int.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_int : IntoValComparable w64 go.int.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

Global Instance into_val_typed_bool : IntoValTyped bool go.bool.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_bool : IntoValComparable bool go.bool.
Proof. constructor. apply go.comparable_bool. Qed.

Global Instance into_val_typed_string : IntoValTyped go_string go.string.
Proof. solve_into_val_typed. Qed.
Global Instance into_val_comparable_string : IntoValComparable go_string go.string.
Proof. constructor. apply go.comparable_ordered. repeat constructor. Qed.

End into_val_typed_instances.

Section inequality_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}.

Ltac solve_ineq lem :=
  iIntros (?) "* _ * HΦ";
  iApply wp_GoInstruction; [intros; repeat econstructor|];
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure;
  iIntros "? $ !>"; rewrite lem; iApply "HΦ"; iFrame.

Global Instance wp_le_uint (v1 v2 : w64) :
  PureWp True (GoLe go.uint (#v1, #v2)%V) #(bool_decide (uint.Z v1 ≤ uint.Z v2)).
Proof. solve_ineq go.le_uint. Qed.
Global Instance wp_lt_uint (v1 v2 : w64) :
  PureWp True (GoLt go.uint (#v1, #v2)%V) #(bool_decide (uint.Z v1 < uint.Z v2)).
Proof. solve_ineq go.lt_uint. Qed.
Global Instance wp_ge_uint (v1 v2 : w64) :
  PureWp True (GoGe go.uint (#v1, #v2)%V) #(bool_decide (uint.Z v2 ≤ uint.Z v1)).
Proof. solve_ineq go.le_uint. Qed.
Global Instance wp_gt_uint (v1 v2 : w64) :
  PureWp True (GoGt go.uint (#v1, #v2)%V) #(bool_decide (uint.Z v2 < uint.Z v1)).
Proof. solve_ineq go.lt_uint. Qed.

Global Instance wp_le_uint64 (v1 v2 : w64) :
  PureWp True (GoLe go.uint64 (#v1, #v2)%V) #(bool_decide (uint.Z v1 ≤ uint.Z v2)).
Proof. solve_ineq go.le_uint64. Qed.
Global Instance wp_lt_uint64 (v1 v2 : w64) :
  PureWp True (GoLt go.uint64 (#v1, #v2)%V) #(bool_decide (uint.Z v1 < uint.Z v2)).
Proof. solve_ineq go.lt_uint64. Qed.
Global Instance wp_ge_uint64 (v1 v2 : w64) :
  PureWp True (GoGe go.uint64 (#v1, #v2)%V) #(bool_decide (uint.Z v2 ≤ uint.Z v1)).
Proof. solve_ineq go.le_uint64. Qed.
Global Instance wp_gt_uint64 (v1 v2 : w64) :
  PureWp True (GoGt go.uint64 (#v1, #v2)%V) #(bool_decide (uint.Z v2 < uint.Z v1)).
Proof. solve_ineq go.lt_uint64. Qed.

Global Instance wp_le_uint32 (v1 v2 : w32) :
  PureWp True (GoLe go.uint32 (#v1, #v2)%V) #(bool_decide (uint.Z v1 ≤ uint.Z v2)).
Proof. solve_ineq go.le_uint32. Qed.
Global Instance wp_lt_uint32 (v1 v2 : w32) :
  PureWp True (GoLt go.uint32 (#v1, #v2)%V) #(bool_decide (uint.Z v1 < uint.Z v2)).
Proof. solve_ineq go.lt_uint32. Qed.
Global Instance wp_ge_uint32 (v1 v2 : w32) :
  PureWp True (GoGe go.uint32 (#v1, #v2)%V) #(bool_decide (uint.Z v2 ≤ uint.Z v1)).
Proof. solve_ineq go.le_uint32. Qed.
Global Instance wp_gt_uint32 (v1 v2 : w32) :
  PureWp True (GoGt go.uint32 (#v1, #v2)%V) #(bool_decide (uint.Z v2 < uint.Z v1)).
Proof. solve_ineq go.lt_uint32. Qed.

Global Instance wp_le_uint16 (v1 v2 : w16) :
  PureWp True (GoLe go.uint16 (#v1, #v2)%V) #(bool_decide (uint.Z v1 ≤ uint.Z v2)).
Proof. solve_ineq go.le_uint16. Qed.
Global Instance wp_lt_uint16 (v1 v2 : w16) :
  PureWp True (GoLt go.uint16 (#v1, #v2)%V) #(bool_decide (uint.Z v1 < uint.Z v2)).
Proof. solve_ineq go.lt_uint16. Qed.
Global Instance wp_ge_uint16 (v1 v2 : w16) :
  PureWp True (GoGe go.uint16 (#v1, #v2)%V) #(bool_decide (uint.Z v2 ≤ uint.Z v1)).
Proof. solve_ineq go.le_uint16. Qed.
Global Instance wp_gt_uint16 (v1 v2 : w16) :
  PureWp True (GoGt go.uint16 (#v1, #v2)%V) #(bool_decide (uint.Z v2 < uint.Z v1)).
Proof. solve_ineq go.lt_uint16. Qed.

Global Instance wp_le_uint8 (v1 v2 : w8) :
  PureWp True (GoLe go.uint8 (#v1, #v2)%V) #(bool_decide (uint.Z v1 ≤ uint.Z v2)).
Proof. solve_ineq go.le_uint8. Qed.
Global Instance wp_lt_uint8 (v1 v2 : w8) :
  PureWp True (GoLt go.uint8 (#v1, #v2)%V) #(bool_decide (uint.Z v1 < uint.Z v2)).
Proof. solve_ineq go.lt_uint8. Qed.
Global Instance wp_ge_uint8 (v1 v2 : w8) :
  PureWp True (GoGe go.uint8 (#v1, #v2)%V) #(bool_decide (uint.Z v2 ≤ uint.Z v1)).
Proof. solve_ineq go.le_uint8. Qed.
Global Instance wp_gt_uint8 (v1 v2 : w8) :
  PureWp True (GoGt go.uint8 (#v1, #v2)%V) #(bool_decide (uint.Z v2 < uint.Z v1)).
Proof. solve_ineq go.lt_uint8. Qed.

Global Instance wp_le_int (v1 v2 : w64) :
  PureWp True (GoLe go.int (#v1, #v2)%V) #(bool_decide (sint.Z v1 ≤ sint.Z v2)).
Proof. solve_ineq go.le_int. Qed.
Global Instance wp_lt_int (v1 v2 : w64) :
  PureWp True (GoLt go.int (#v1, #v2)%V) #(bool_decide (sint.Z v1 < sint.Z v2)).
Proof. solve_ineq go.lt_int. Qed.
Global Instance wp_ge_int (v1 v2 : w64) :
  PureWp True (GoGe go.int (#v1, #v2)%V) #(bool_decide (sint.Z v2 ≤ sint.Z v1)).
Proof. solve_ineq go.le_int. Qed.
Global Instance wp_gt_int (v1 v2 : w64) :
  PureWp True (GoGt go.int (#v1, #v2)%V) #(bool_decide (sint.Z v2 < sint.Z v1)).
Proof. solve_ineq go.lt_int. Qed.

Global Instance wp_le_int64 (v1 v2 : w64) :
  PureWp True (GoLe go.int64 (#v1, #v2)%V) #(bool_decide (sint.Z v1 ≤ sint.Z v2)).
Proof. solve_ineq go.le_int64. Qed.
Global Instance wp_lt_int64 (v1 v2 : w64) :
  PureWp True (GoLt go.int64 (#v1, #v2)%V) #(bool_decide (sint.Z v1 < sint.Z v2)).
Proof. solve_ineq go.lt_int64. Qed.
Global Instance wp_ge_int64 (v1 v2 : w64) :
  PureWp True (GoGe go.int64 (#v1, #v2)%V) #(bool_decide (sint.Z v2 ≤ sint.Z v1)).
Proof. solve_ineq go.le_int64. Qed.
Global Instance wp_gt_int64 (v1 v2 : w64) :
  PureWp True (GoGt go.int64 (#v1, #v2)%V) #(bool_decide (sint.Z v2 < sint.Z v1)).
Proof. solve_ineq go.lt_int64. Qed.

Global Instance wp_le_int32 (v1 v2 : w32) :
  PureWp True (GoLe go.int32 (#v1, #v2)%V) #(bool_decide (sint.Z v1 ≤ sint.Z v2)).
Proof. solve_ineq go.le_int32. Qed.
Global Instance wp_lt_int32 (v1 v2 : w32) :
  PureWp True (GoLt go.int32 (#v1, #v2)%V) #(bool_decide (sint.Z v1 < sint.Z v2)).
Proof. solve_ineq go.lt_int32. Qed.
Global Instance wp_ge_int32 (v1 v2 : w32) :
  PureWp True (GoGe go.int32 (#v1, #v2)%V) #(bool_decide (sint.Z v2 ≤ sint.Z v1)).
Proof. solve_ineq go.le_int32. Qed.
Global Instance wp_gt_int32 (v1 v2 : w32) :
  PureWp True (GoGt go.int32 (#v1, #v2)%V) #(bool_decide (sint.Z v2 < sint.Z v1)).
Proof. solve_ineq go.lt_int32. Qed.

Global Instance wp_le_int16 (v1 v2 : w16) :
  PureWp True (GoLe go.int16 (#v1, #v2)%V) #(bool_decide (sint.Z v1 ≤ sint.Z v2)).
Proof. solve_ineq go.le_int16. Qed.
Global Instance wp_lt_int16 (v1 v2 : w16) :
  PureWp True (GoLt go.int16 (#v1, #v2)%V) #(bool_decide (sint.Z v1 < sint.Z v2)).
Proof. solve_ineq go.lt_int16. Qed.
Global Instance wp_ge_int16 (v1 v2 : w16) :
  PureWp True (GoGe go.int16 (#v1, #v2)%V) #(bool_decide (sint.Z v2 ≤ sint.Z v1)).
Proof. solve_ineq go.le_int16. Qed.
Global Instance wp_gt_int16 (v1 v2 : w16) :
  PureWp True (GoGt go.int16 (#v1, #v2)%V) #(bool_decide (sint.Z v2 < sint.Z v1)).
Proof. solve_ineq go.lt_int16. Qed.

Global Instance wp_le_int8 (v1 v2 : w8) :
  PureWp True (GoLe go.int8 (#v1, #v2)%V) #(bool_decide (sint.Z v1 ≤ sint.Z v2)).
Proof. solve_ineq go.le_int8. Qed.
Global Instance wp_lt_int8 (v1 v2 : w8) :
  PureWp True (GoLt go.int8 (#v1, #v2)%V) #(bool_decide (sint.Z v1 < sint.Z v2)).
Proof. solve_ineq go.lt_int8. Qed.
Global Instance wp_ge_int8 (v1 v2 : w8) :
  PureWp True (GoGe go.int8 (#v1, #v2)%V) #(bool_decide (sint.Z v2 ≤ sint.Z v1)).
Proof. solve_ineq go.le_int8. Qed.
Global Instance wp_gt_int8 (v1 v2 : w8) :
  PureWp True (GoGt go.int8 (#v1, #v2)%V) #(bool_decide (sint.Z v2 < sint.Z v1)).
Proof. solve_ineq go.lt_int8. Qed.

End inequality_instances.

Section __struct_test.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}.

Record foo_t :=
  mk {
      a : w64;
      b : go_string;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {|
    into_val_def := λ v, StructV {[ "b"%go := #v.(b); "a"%go := #v.(a) ]};
    zero_val := mk (zero_val _) (zero_val _)
  |}.

Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go go.uint64); (go.EmbeddedField "b"%go go.string)].
Definition foo : go.type := go.Named "foo"%go [].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : to_underlying foo = foo_impl
  }.

Context `{!foo_type_assumptions}.

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

Global Instance settable_foo : Settable foo_t :=
  settable! mk < a; b >.

Ltac solve_wp_struct_field_set :=
  iIntros (?) "* _ *"; iIntros "Hwp";
  rewrite [in (into_val (V:=foo_t))]into_val_unseal; wp_pure_lc "Hlc";
  iSpecialize ("Hwp" with "[$]"); simpl; iExactEq "Hwp"; do 4 f_equal;
  repeat (rewrite insert_insert; destruct decide; [done| (done || f_equal)]).

Ltac solve_wp_struct_field_get :=
  iIntros (?) "* _ *"; iIntros "Hwp";
  rewrite [in (into_val (V:=foo_t))]into_val_unseal; wp_apply wp_StructFieldGet_untyped; last done;
  repeat (rewrite lookup_insert_ne //; []); rewrite lookup_insert //.

Global Instance wp_StructFieldSet_foo_a (v : foo_t) (a' : w64) :
  PureWp True (StructFieldSet "a" (#v, #a')%V)
         (#(set a (const a') v)).
Proof. solve_wp_struct_field_set. Qed.

Global Instance wp_StructFieldSet_foo_b (v : foo_t) b' :
  PureWp True (StructFieldSet "b" (#v, #b')%V)
         (#(set b (const b') v)).
Proof. solve_wp_struct_field_set. Qed.

Global Instance wp_StructFieldGet_foo_a (v : foo_t) :
  PureWp True (StructFieldGet "a" #v) #v.(a).
Proof. solve_wp_struct_field_get. Qed.

Global Instance wp_StructFieldGet_foo_b (v : foo_t) :
  PureWp True (StructFieldGet "b" #v) #v.(b).
Proof. solve_wp_struct_field_get. Qed.

Global Instance into_val_typed_foo  : IntoValTyped foo_t foo.
Proof using H core_sem pre_sem.
  split.
  - iIntros "* _ HΦ".
    rewrite go.alloc_underlying foo_underlying.
    rewrite go.alloc_struct.
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.struct_field_ref_underlying foo_underlying.
    wp_pures. simpl.
    wp_apply wp_GoPrealloc. iIntros (l) "_".

    wp_pures. wp_apply wp_alloc. iIntros (?) "?".
    wp_pures. case_bool_decide; subst; wp_pures; last (wp_apply wp_AngelicExit).

    wp_pures. wp_apply wp_alloc. iIntros (?) "?".
    wp_pures. case_bool_decide; subst; wp_pures; last (wp_apply wp_AngelicExit).

    iApply "HΦ". iFrame.
  - iIntros "* Hl HΦ".
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.load_underlying foo_underlying.
    rewrite go.struct_field_ref_underlying foo_underlying.
    rewrite [in (_ foo_t)]into_val_unseal.
    rewrite go.load_struct /=. iNamed "Hl".

    wp_pures. wp_apply (wp_load with "[$a]"). iIntros "a". wp_pures.

    wp_pures. wp_apply (wp_load with "[$b]"). iIntros "b". wp_pures.

    rewrite insert_empty. wp_pures. iApply "HΦ". iFrame.
  - iIntros "* Hl HΦ".
    rewrite [in (_ (foo_t))]typed_pointsto_unseal /=.
    rewrite go.store_underlying foo_underlying.
    rewrite go.struct_field_ref_underlying foo_underlying.
    rewrite go.store_struct /=. iNamed "Hl".

    wp_pures. wp_apply (wp_store with "a"). iIntros "a".
    wp_pures. wp_apply (wp_store with "b"). iIntros "b".

    iApply "HΦ". iFrame.
Qed.

Lemma wp_test :
  {{{ True }}}
    (let: "i" := #(interface.mk (go.uint64) #(W64 0)) in
     let: "z" := MethodResolve (go.error) "foo" #() "i" in
     #()
    )
  {{{ RET #(); True }}}.
Proof.
  iIntros "% _ HΦ". wp_pures.
  rewrite go.method_interface //.
  2:{ unfold is_interface_type. erewrite go.predeclared_underlying.
      2:{ admit. }
      done. }
  wp_pures.
Abort.

End __struct_test.
