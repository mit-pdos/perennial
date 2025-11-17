Require Export New.code.sync.atomic.
From New.proof Require Import proof_prelude.

(* copy of proofgen output from translating atomic.Pointer *)
(* type atomic.noCopy *)
Module noCopy.
Section def.
Context `{ffi_syntax}.
Record t := mk {
}.
End def.
End noCopy.

Section instances.
Context `{ffi_syntax}.
#[local] Transparent atomic.noCopy.
#[local] Typeclasses Transparent atomic.noCopy.

Global Instance noCopy_wf : struct.Wf atomic.noCopy.
Proof. apply _. Qed.

Global Instance into_val_noCopy : IntoVal noCopy.t :=
  {| to_val_def v :=
    struct.val_aux atomic.noCopy [
    ]%struct
  |}.

Global Program Instance into_val_typed_noCopy : IntoValTyped noCopy.t atomic.noCopy :=
{|
  default_val := noCopy.mk;
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_noCopy:
  PureWp True
    (struct.make #atomic.noCopy (alist_val [
    ]))%struct
    #(noCopy.mk).
Proof. solve_struct_make_pure_wp. Qed.

End instances.

(* type atomic.Pointer *)
Module Pointer.
Section def.
Context `{ffi_syntax}.

Definition ty (T : go_type) : go_type := structT [
  "_0" :: arrayT (W64 0) ptrT;
  "_1" :: atomic.noCopy;
  "v" :: ptrT
]%struct.
#[global] Typeclasses Opaque ty.
#[global] Opaque ty.
Record t `{!IntoVal T'} `{!IntoValTyped T' T} := mk {
  _0' : (vec loc (uint.nat (W64 0)));
  _1' : noCopy.t;
  v' : loc;
}.
End def.
End Pointer.

#[local] Transparent Pointer.ty.
Arguments Pointer.mk {_} { T' } {_ T _} .
Arguments Pointer.t {_} T' {_ T _} .

Section instances.
Context `{ffi_syntax}.
Context`{!IntoVal T'} `{!IntoValTyped T' T} .
#[local] Transparent atomic.Pointer.
#[local] Typeclasses Transparent atomic.Pointer.

Global Instance Pointer_wf : struct.Wf (Pointer.ty T).
Proof. apply _. Qed.

Global Instance settable_Pointer : Settable (Pointer.t T') :=
  settable! (Pointer.mk (T:=T)) < Pointer._0'; Pointer._1'; Pointer.v' >.
Global Instance into_val_Pointer : IntoVal (Pointer.t T') :=
  {| to_val_def v :=
    struct.val_aux (Pointer.ty T) [
    "_0" ::= #(Pointer._0' v);
    "_1" ::= #(Pointer._1' v);
    "v" ::= #(Pointer.v' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Pointer : IntoValTyped (Pointer.t T') (Pointer.ty T) :=
{|
  default_val := Pointer.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Pointer__0 : IntoValStructField "_0" (Pointer.ty T) Pointer._0'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Pointer__1 : IntoValStructField "_1" (Pointer.ty T) Pointer._1'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Pointer_v : IntoValStructField "v" (Pointer.ty T) Pointer.v'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_type_Pointer :
  PureWp True
    (atomic.Pointer #T)
    #(Pointer.ty T).
Proof. solve_type_pure_wp. Qed.


Global Instance wp_struct_make_Pointer _0' _1' v':
  PureWp True
    (struct.make #(Pointer.ty T) (alist_val [
      "_0" ::= #_0';
      "_1" ::= #_1';
      "v" ::= #v'
    ]))%struct
    #(Pointer.mk _0' _1' v').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Pointer_struct_fields_split `{!BoundedTypeSize T} dq l (v : (Pointer.t T')) :
  StructFieldsSplit dq l v (
    "H_0" ∷ l ↦s[(Pointer.ty T) :: "_0"]{dq} v.(Pointer._0') ∗
    "H_1" ∷ l ↦s[(Pointer.ty T) :: "_1"]{dq} v.(Pointer._1') ∗
    "Hv" ∷ l ↦s[(Pointer.ty T) :: "v"]{dq} v.(Pointer.v')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (Pointer._0' v)) ((Pointer.ty T)) "_0"%go.
  simpl_one_flatten_struct (# (Pointer._1' v)) ((Pointer.ty T)) "_1"%go.

  solve_field_ref_f.
Qed.

End instances.
(* end copy of proofgen output *)
