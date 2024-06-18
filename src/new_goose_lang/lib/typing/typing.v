From Perennial.new_goose_lang Require Export lib.typing.impl.

(** * Typed data representations for struct and slice *)
Module slice.
Record t := mk { ptr: loc; sz: u64; cap: u64; }.
Notation nil := slice_nil.

Section goose_lang.
  Context `{ffi_semantics}.
  Definition val (s: slice.t) : val := (#s.(slice.ptr), #s.(slice.sz), #s.(slice.cap)).
End goose_lang.
End slice.

Module struct.
Section goose_lang.
  Context `{ffi_syntax}.

  Infix "=?" := (String.eqb).

  Fixpoint val (d : struct.descriptor) (field_vals: list (string*val)): val :=
    match d with
    | [] => (#())
    | (f,ft)::fs => (default (zero_val ft) (assocl_lookup field_vals f), val fs field_vals)
    end.
End goose_lang.
End struct.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (@pair string val f%string v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.

(** * Pure Coq reasoning principles *)
Section typing.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.

  Program Definition go_type_ind :=
    λ (P : go_type → Prop) (f : P boolT) (f0 : P uint8T) (f1 : P uint16T) (f2 : P uint32T)
      (f3 : P uint64T) (f4 : P int8T) (f5 : P int16T) (f6 : P int32T) (f7 : P int64T)
      (f8 : P stringT) (f9 : ∀ elem : go_type, P elem → P (sliceT elem))
      (f10 : ∀ (decls : list (string * go_type)) (Hfields : ∀ t, In t decls.*2 → P t), P (structT decls))
      (f11 : P ptrT) (f12 : P funcT) (f13 : P interfaceT)
      (f14 : ∀ key : go_type, P key → ∀ elem : go_type, P elem → P (mapT key elem))
      (f15 : ∀ elem : go_type, P elem → P (chanT elem)),
    fix F (g : go_type) : P g :=
      match g as g0 return (P g0) with
      | boolT => f
      | uint8T => f0
      | uint16T => f1
      | uint32T => f2
      | uint64T => f3
      | int8T => f4
      | int16T => f5
      | int32T => f6
      | int64T => f7
      | stringT => f8
      | sliceT elem => f9 elem (F elem)
      | structT decls => f10 decls _
      | ptrT => f11
      | funcT => f12
      | interfaceT => f13
      | mapT key elem => f14 key (F key) elem (F elem)
      | chanT elem => f15 elem (F elem)
      end.
  Obligation 1.
  intros.
  revert H.
  enough (Forall P decls.*2).
  1:{
    intros.
    rewrite List.Forall_forall in H.
    apply H. done.
  }
  induction decls; first done.
  destruct a. apply Forall_cons. split.
  { apply F. }
  { apply IHdecls. }
  Defined.

  Inductive has_go_type : val → go_type → Prop :=
  | has_go_type_bool (b : bool) : has_go_type #b boolT
  | has_go_type_uint64 (x : w64) : has_go_type #x uint64T
  | has_go_type_uint32 (x : w32) : has_go_type #x uint32T
  | has_go_type_uint16 : has_go_type nil uint16T
  | has_go_type_uint8 (x : w8) : has_go_type #x uint8T

  | has_go_type_int64 (x : w64) : has_go_type #x int64T
  | has_go_type_int32 (x : w32) : has_go_type #x int32T
  | has_go_type_int16 : has_go_type nil int16T
  | has_go_type_int8 (x : w8) : has_go_type #x int8T

  | has_go_type_string (s : string) : has_go_type #(str s) stringT
  | has_go_type_slice elem (s : slice.t) : has_go_type (slice.val s) (sliceT elem)
  | has_go_type_slice_nil elem : has_go_type slice.nil (sliceT elem)

  | has_go_type_struct
      (d : struct.descriptor) fvs
      (Hfields : ∀ f t, In (f, t) d → has_go_type (default (zero_val t) (assocl_lookup fvs f)) t)
    : has_go_type (struct.val d fvs) (structT d)
  | has_go_type_ptr (l : loc) : has_go_type #l ptrT
  | has_go_type_func f e v : has_go_type (RecV f e v) funcT
  | has_go_type_func_nil : has_go_type nil funcT

  (* FIXME: interface_val *)
  | has_go_type_interface (s : slice.t) : has_go_type (slice.val s) interfaceT
  | has_go_type_interface_nil : has_go_type interface_nil interfaceT

  | has_go_type_mapT kt vt (l : loc) : has_go_type #l (mapT kt vt)
  | has_go_type_chanT t (l : loc) : has_go_type #l (chanT t)
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    induction t using go_type_ind; try econstructor.
    replace (zero_val (structT decls)) with (struct.val decls []).
    {
      econstructor. intros. simpl. apply Hfields.
      apply in_map_iff. eexists _.
      split; last done. done.
    }
    induction decls.
    { simpl. replace (#()) with (struct.val [] []) by done. econstructor. }
    destruct a. simpl.
    f_equal.
    apply IHdecls.
    intros.
    apply Hfields.
    simpl. right. done.
  Qed.

  Lemma has_go_type_len {v t} :
    has_go_type v t ->
    length (flatten_struct v) = (go_type_size t).
  Proof.
    rewrite go_type_size_unseal.
    induction 1; simpl; auto.
    induction d.
    { done. }
    destruct a. cbn.
    rewrite app_length.
    rewrite IHd.
    { f_equal. apply H. by left. }
    { clear H IHd. intros. apply Hfields. by right. }
    { intros. apply H. simpl. by right. }
  Qed.

End typing.
