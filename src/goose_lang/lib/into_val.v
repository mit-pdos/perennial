From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang.lib Require Import typed_mem slice.slice struct.struct.

Class IntoVal {ext: ext_op} V :=
  { to_val: V -> val;
    IntoVal_def: V;
    IntoVal_eq: ∀ v v', to_val v = to_val v' -> v = v'
  }.

Class IntoValForType {ext V} (H: @IntoVal ext V) {ext_ty: ext_types ext} (t:ty) :=
    { def_is_zero: to_val IntoVal_def = zero_val t;
      to_val_has_zero: has_zero t;
      (* TODO: this isn't necessary, but it seems reasonable *)
      to_val_ty: forall v, val_ty (to_val v) t; }.

(** instances for IntoVal *)
Section instances.
  Context {ext: ext_op} {ext_ty: ext_types ext}.
  Global Instance u64_IntoVal : IntoVal u64 :=
    {| to_val := λ (x: u64), #x;
       IntoVal_def := U64 0;
       IntoVal_eq := ltac:(congruence) |}.

  Global Instance u64_IntoVal_uint64T : IntoValForType u64_IntoVal uint64T.
  Proof.
    constructor; auto.
  Qed.

  Global Instance loc_IntoVal : IntoVal loc :=
    {| to_val := λ (l: loc), #l;
       IntoVal_def := null;
       IntoVal_eq := ltac:(congruence)
    |}.

  Global Instance loc_IntoVal_struct_ptr t : IntoValForType loc_IntoVal (struct.ptrT t).
  Proof.
    constructor; auto.
  Qed.

  Global Instance loc_IntoVal_ref t : IntoValForType loc_IntoVal (refT t).
  Proof.
    constructor; auto.
  Qed.

  Global Instance slice_IntoVal : IntoVal Slice.t.
    refine
    {| to_val := slice_val;
       IntoVal_def := Slice.nil;
       IntoVal_eq := _
    |}.
    destruct v, v'.
    rewrite /slice_val /=.
    intro H; inversion H; eauto.
  Defined.

  Global Instance slice_IntoVal_ref t : IntoValForType slice_IntoVal (slice.T t).
  Proof.
    constructor; auto.
    intros.
    apply slice_val_ty.
  Qed.

End instances.
