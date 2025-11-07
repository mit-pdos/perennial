From New.golang.theory Require Export proofmode.
From New.experiments Require Export glob.
From Perennial Require Import base.
From Perennial.Helpers Require Import List.
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

Lemma wp_PackageInitCheck {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    GoInstruction (PackageInitCheck pkg) #() @ stk; E
  {{{ RET #(bool_decide (is_Some (s !! pkg))); own_go_state s }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  iIntros "* %Hstep".
  inv Hstep; last by inv Hpure.
  iSplitR; first by iIntros "$".
  iIntros "_".
  rewrite !bool_decide_decide.
  destruct decide at 2.
  { exfalso. clear -e. done. }
  2:{
    simpl.
    exfalso. set_solver.
  }
  simpl. wp_pures. rewrite decide_True. iApply "HΦ".
  iApply "HΦ". iFrame.
Qed.

  Eval simpl in (decide (pkg ∈ s')).

  (bool_decide (pkg ∈ s')).

  simpl.

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

Global Instance into_val_typed_uint64 : IntoValTyped w64 go.uint64.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint32 : IntoValTyped w32 go.uint32.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint16 : IntoValTyped w16 go.uint16.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint8 : IntoValTyped w8 go.uint8.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_int64 : IntoValTyped w64 go.int64.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_int32 : IntoValTyped w32 go.int32.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_int16 : IntoValTyped w16 go.int16.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_int8 : IntoValTyped w8 go.int8.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_bool : IntoValTyped bool go.bool.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_string : IntoValTyped go_string go.string.
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_slice t : IntoValTyped slice.t (go.SliceType t).
Proof using Hvalid. solve_into_val_typed. Qed.

Global Instance into_val_typed_chan t b : IntoValTyped chan.t (go.ChannelType b t).
Proof using Hvalid. solve_into_val_typed. Qed.

Lemma seqZ_succ start n :
  0 ≤ n →
  seqZ start (Z.succ n) = seqZ start n ++ [start + n].
Proof.
  intros H. rewrite /seqZ Z2Nat.inj_succ; last lia.
  rewrite seq_S fmap_app /=. f_equal. f_equal. lia.
Qed.

Global Instance into_val_typed_array `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t} n
  : IntoValTyped (array.t t V n) (go.ArrayType n t).
Proof using Hvalid.
  split.
  - admit.
  - iIntros "* Hl HΦ".
    rewrite go.load_array. case_decide.
    { wp_pures. wp_apply wp_AngelicExit. }
    wp_pure. wp_pure. rewrite typed_pointsto_unseal /=.
    iDestruct "Hl" as "[%Hlen Hl]".

    assert (∃ m, n = m ∧ 0 ≤ m ≤ n) as (m & Heq & Hm) by (exists n; lia).
    rewrite [in #(W64 n)]Heq.
    iEval (rewrite <- Heq, into_val_unseal) in "HΦ".
    simpl. destruct v as [v]. simpl in *.
    replace (v) with (take (Z.to_nat m) v).
    2:{ rewrite take_ge //. lia. }
    clear Heq.
    set (f := #(func.mk _ _ _)).
    iLöb as "IH" forall (m Hm Φ).

    wp_pures. fold f.
    case_bool_decide as Heq.
    { wp_pures. replace m with 0 by word. rewrite into_val_unseal /=. by iApply "HΦ". }
    wp_pure. wp_pure. set (m':=m-1).
    replace (word.sub _ _) with (W64 m') by word.
    replace (Z.to_nat m) with (S (Z.to_nat m'))%nat by word.
    pose proof (list_lookup_lt v (Z.to_nat m')) as [ve Hlookup]; first word.
    erewrite take_S_r; last done.
    rewrite big_sepL_app /=. iDestruct "Hl" as "(Hl & Hlast & _)".
    wp_apply ("IH" with "[] Hl"); first word. iIntros "[_ Hl]".
    wp_pures. rewrite go.index_ref_array. wp_pures. wp_apply (wp_load with "[Hlast]").
    { iExactEq "Hlast". f_equal. f_equal. rewrite length_take. word. }
    iIntros "Hlast". rewrite length_app length_take. wp_pures. rewrite fmap_app /=.
    iApply "HΦ". iFrame. iSplitR; first word.
    iSplitL; last done. iExactEq "Hlast". f_equal. f_equal. word.
  - admit.
Admitted.

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
