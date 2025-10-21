From New.golang.theory Require Export proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {Hvalid : go.ContextValid}.

Program Global Instance into_val_proof_loc : IntoValProof loc :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_w64 : IntoValProof w64 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_w32 : IntoValProof w32 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_w16 : IntoValProof w16 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_w8 : IntoValProof w8 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_bool : IntoValProof bool :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_string : IntoValProof go_string :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_proof_slice : IntoValProof slice.t :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

(* Helper lemmas for establishing [IntoValTyped] *)
Local Lemma wp_untyped_load l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    ! #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof. rewrite to_val_unseal. apply lifting.wp_load. Qed.

Local Lemma wp_untyped_store l v v' s E :
  {{{ ▷ heap_pointsto l (DfracOwn 1) v }}}
    #l <- v' @ s; E
  {{{ RET #(); heap_pointsto l (DfracOwn 1) v' }}}.
Proof.
  rewrite to_val_unseal. iIntros "% Hl HΦ". wp_call.
  wp_apply (wp_prepare_write with "Hl"). iIntros "[Hl Hl']".
  wp_pures. by iApply (wp_finish_store with "[$Hl $Hl']").
Qed.

Existing Class go.is_primitive.
#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.

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

Local Ltac solve_into_val_typed := constructor; [solve_wp_load|solve_wp_store].

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

(* Using [vec] here because the [to_val] must be a total function that always
   meets [has_go_type]. An alternative could be a sigma type. *)
Program Global Instance into_val_typed_array `{!IntoVal V} `{!IntoValTyped V t} n :
  IntoValTyped (vec V n) (arrayT n t) :=
{| default_val := vreplicate n (default_val _) |}.
Next Obligation.
  rewrite to_val_unseal /=.
  solve_has_go_type.
  induction v as [|].
  - apply (has_go_type_array 0 t []); done.
  - simpl in *.
    inversion IHv. subst.
    pose proof (has_go_type_array (S (length a)) t (#h::a) ltac:(done)) as Ht.
    simpl in Ht. apply Ht. intros ? [|].
    + subst. apply to_val_has_go_type.
    + apply Helems. done.
Qed.
Next Obligation.
  intros.
  rewrite to_val_unseal zero_val_eq /=.
  rewrite -zero_val_unseal -default_val_eq_zero_val.
  induction n; first done. simpl. f_equal. apply IHn.
Qed.
Final Obligation.
rewrite to_val_unseal.
intros. intros ?? Heq.
simpl in Heq.
induction x.
{ rewrite (VectorSpec.nil_spec y) //. }
destruct y using vec_S_inv.
simpl in *.
injection Heq as Heq1 Heq.
apply to_val_inj in Heq1. subst.
f_equal. by apply IHx.
Qed.

Program Global Instance into_val_typed_func : IntoValTyped func.t funcT :=
{| default_val := func.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => [[???] [???]] /= [=] //. naive_solver.
Qed.
Final Obligation. solve_decision. Qed.

Program Global Instance into_val_typed_interface : IntoValTyped interface.t interfaceT :=
{| default_val := interface.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation.
  rewrite to_val_unseal => [x y] Heq.
  destruct x as [|], y as [|].
  {
    simpl in *.
    injection Heq as Heq1 Heq2.
    apply to_val_inj in Heq1. subst. done.
  }
  all: first [discriminate | reflexivity].
Qed.
Final Obligation.
  solve_decision.
Qed.

Program Global Instance into_val_typed_unit : IntoValTyped unit (structT []) :=
{| default_val := tt |}.
Next Obligation.
  intros [].
  replace (#()) with (struct.val_aux (structT []) []).
  2:{ rewrite struct.val_aux_unseal //. }
  by constructor.
Qed.
Next Obligation. rewrite zero_val_eq /= struct.val_aux_unseal //. Qed.
Final Obligation.
  intros ???. destruct x, y. done.
Qed. *)

End into_val_instances.


Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!NamedUnderlyingTypes}.

Context `{!go.MemOps}.
Program Global Instance into_val_typed_uint64 : IntoValTyped loc go.uint64.
Next Obligation.
  iIntros "* Hl HΦ".
  rewrite go.load_primitive; [|constructor].
  wp_pures.
Admitted.
Final Obligation. Admitted.

Program Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Next Obligation.
  iIntros "* Hl HΦ".
  rewrite go.load_primitive; [|constructor].
  wp_pures.
Admitted.
Final Obligation. Admitted.

Record foo_t :=
  mk {
      a : w64;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {| to_val_def := λ v, (#v.(a), #())%V; zero_val := (mk (zero_val _)) |}.

Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go go.uint64)].
Definition foo : go.type := go.Named "foo"%go [].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : named_to_underlying "foo"%go [] = foo_impl
  }.

Context `{!foo_type_assumptions}.

(* TODO: struct field_ref. One option is to have field_ref_f be a totally opaque
   function.  All that really matters is it's a deterministic computation and
   that it agrees with allocation.
   E.g. it really doesn't matter if struct fields are packed or not, nor if
   they're in the same order as source code.
 *)
(* TODO: for struct values, what about using a gmap rather than list val?
   Induction principle might be screwed up. *)

Program Global Instance into_val_proof_w64 : IntoValProof w64 :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := heap_pointsto l dq #v |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_foo_inj : IntoValProof foo_t :=
  {| typed_pointsto_def _ _ _ _ _ _ l dq v := (struct_field_ref foo "a"%go l ↦{dq} v.(a))%I |}.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Admitted.
Next Obligation. solve_decision. Qed.

Lemma foo_split l dq (v : foo_t) :
  l ↦{dq} v ⊢ (struct_field_ref foo "a"%go l) ↦{dq} v.(a).
Proof. done. Qed.

Program Global Instance into_val_typed_foo  : IntoValTyped foo_t foo.
Next Obligation.
  iIntros "* Hl HΦ".
  iEval (rewrite go.load_underlying /= foo_underlying go.load_struct /=).
  wp_pures. wp_bind.
  iDestruct (foo_split with "Hl") as "Hl".
  Opaque typed_pointsto. (* FIXME: seal typed_pointsto *)
  iEval (rewrite go.struct_field_ref_underlying /= foo_underlying /foo_impl) in "Hl".
  wp_apply (wp_load (t:=go.uint64) with "Hl").
  iIntros "Hl".
  wp_pures.
  (* FIXME: construct StructVal. Have pure op to insert into struct val. Can
     start from empty struct val. Can give list-like notation. *)
Admitted.

(* TODO: Maybe aggregate all the built-in dynamic functions into one instruction? *)

Context `{!GoContext}.
Context `{!MemOps}.

Record foo_t :=
  mk {
      a : w64;
    }.
Global Instance into_val_foo : IntoVal foo_t :=
  {| to_val_def := λ v, (#v.(a), #())%V; zero_val := (mk (zero_val _)) |}.

Definition foo : go.type := go.Named "foo"%go [].
Definition foo_impl : go.type := go.StructType [(go.FieldDecl "a"%go uint64)].

Class foo_type_assumptions : Prop :=
  {
    foo_underlying : named_to_underlying "foo"%go [] = foo_impl
  }.

Context `{!foo_type_assumptions}.

Goal goose_lang.size (go.ArrayType 3 foo) = 3.
  rewrite size_array size_underlying /= foo_underlying
    size_struct /= size_primitive //. constructor.
Qed.

Goal load (go.ArrayType 3 foo) = (λ: "l", ! "l")%V.
  rewrite is_load_array /=. vm_compute Z.add.
  rewrite is_load_underlying /= foo_underlying.
  rewrite is_load_struct /=.
