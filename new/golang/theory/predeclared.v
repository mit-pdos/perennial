From New.golang.theory Require Export proofmode.
From New.experiments Require Export glob.
From Perennial Require Import base.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Set Default Proof Using "Type".

Section mem_lemmas.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {Hvalid : go.CoreSemantics}.

(* Helper lemmas for establishing [IntoValTyped] *)
Local Lemma wp_untyped_load l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    ! #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof. rewrite into_val_unseal. apply lifting.wp_load. Qed.

Local Lemma wp_untyped_store l v v' s E :
  {{{ ▷ heap_pointsto l (DfracOwn 1) v }}}
    #l <- v' @ s; E
  {{{ RET #(); heap_pointsto l (DfracOwn 1) v' }}}.
Proof.
  rewrite into_val_unseal. iIntros "% Hl HΦ". wp_call.
  wp_apply (wp_prepare_write with "Hl"). iIntros "[Hl Hl']".
  wp_pures. by iApply (wp_finish_store with "[$Hl $Hl']").
Qed.

Lemma wp_GoPrealloc {stk E} :
  {{{ True }}}
    GoInstruction GoPrealloc #() @ stk; E
  {{{ (l : loc), RET #l; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_apply (wp_GoInstruction []).
  { intros. eexists #null. econstructor. econstructor. }
  iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iFrame. iSplitR. { by iIntros "$". }
  iIntros "_". simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_AngelicExit Φ s E :
  ⊢ WP GoInstruction AngelicExit #() @ s; E {{ Φ }}.
Proof.
  iLöb as "IH".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iFrame. iSplitR. { by iIntros "$". }
  iIntros "_". simpl. iApply "IH".
Qed.

Existing Class go.is_primitive.
#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.
Existing Class go.is_primitive_zero_val.
#[local] Hint Extern 1 (go.is_primitive_zero_val ?t ?v) => constructor : typeclass_instances.

Local Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite go.alloc_primitive typed_pointsto_unseal /= into_val_unseal;
  wp_pures; by wp_apply wp_alloc_untyped.

Local Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  rewrite go.load_primitive;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (wp_untyped_load with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Local Ltac solve_wp_store :=
  iIntros "* Hl HΦ";
  rewrite go.store_primitive;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (wp_untyped_store with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Local Ltac solve_into_val_typed := constructor; [solve_wp_alloc|solve_wp_load|solve_wp_store].

Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_w64 : IntoValTyped w64 go.uint64.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_w32 : IntoValTyped w32 go.uint32.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_w16 : IntoValTyped w16 go.uint16.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_w8 : IntoValTyped w8 go.uint8.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_bool : IntoValTyped bool go.bool.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_string : IntoValTyped go_string go.string.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_slice t : IntoValTyped slice.t (go.SliceType t).
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_chan t b : IntoValTyped chan.t (go.ChannelType b t).
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_array `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t} n
  : IntoValTyped (array.t t V n) (go.ArrayType n t).
Proof using Hvalid.
  split.
  - admit.
  - iIntros "* Hl HΦ".
    rewrite typed_pointsto_unseal /=.
    rewrite go.load_array. simpl.
    iDestruct "Hl" as "[%Hlen Hl]".
    assert (0 ≤ n) by lia.
    iCombineNamed "*" as "H".
    iStopProof. revert v Hlen. pattern n.
    revert n H. apply natlike_ind.
    + intros. iStartProof. iNamed 1. wp_pures.
      wp_pures. rewrite into_val_unseal /=.
      destruct v as [v]. simpl in *. destruct v; try done.
      simpl. by iApply "HΦ".
    + intros n Hnz IH.
Admitted. (* FIXME: prove these *)

End mem_lemmas.

Section __struct_test.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} `{!go.CoreSemantics}.

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
  PureWp True (GoInstruction (StructFieldSet "a") (#v, #a')%V)
         (#(set a (const a') v)).
Proof. solve_wp_struct_field_set. Qed.

Global Instance wp_StructFieldSet_foo_b (v : foo_t) b' :
  PureWp True (GoInstruction (StructFieldSet "b") (#v, #b')%V)
         (#(set b (const b') v)).
Proof. solve_wp_struct_field_set. Qed.

Global Instance wp_StructFieldGet_foo_a (v : foo_t) :
  PureWp True (GoInstruction (StructFieldGet "a") #v) #v.(a).
Proof. solve_wp_struct_field_get. Qed.

Global Instance wp_StructFieldGet_foo_b (v : foo_t) :
  PureWp True (GoInstruction (StructFieldGet "b") #v) #v.(b).
Proof. solve_wp_struct_field_get. Qed.

Lemma bool_decide_inj `(f : A → B) `{!Inj eq eq f} a a' `{!EqDecision A}
  `{!EqDecision B}
  : bool_decide (f a = f a') = bool_decide (a = a').
Proof.
  case_bool_decide.
  { eapply inj in H1; last done. rewrite bool_decide_true //. }
  { rewrite bool_decide_false //.
    intros HR. apply H1. subst. done. }
Qed.

Global Instance wp_eq `{!IntoVal V} `{!IntoValComparable V} (v1 v2 : V) :
  PureWp True (BinOp EqOp #v1 #v2) #(bool_decide (v1 = v2)).
Proof.
  pose proof wp_eq_val.
  iIntros (?) "* _ * HΦ".
  wp_pure_lc "Hl"; [ split; apply into_val_comparable | ].
  rewrite bool_decide_inj.
  iApply "HΦ". iFrame.
Qed.

Global Instance into_val_typed_foo  : IntoValTyped foo_t foo.
Proof using H H0.
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

End __struct_test.
