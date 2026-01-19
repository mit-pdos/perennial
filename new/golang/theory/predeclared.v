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
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite go.alloc_predeclared typed_pointsto_unseal /=;
  wp_pures; by wp_apply _internal_wp_alloc_untyped.

Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  rewrite go.load_predeclared;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_read with "Hl");
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

Local Set Default Proof Using "All".
Global Instance into_val_typed_uint64 : IntoValTyped w64 go.uint64.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint32 : IntoValTyped w32 go.uint32.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint16 : IntoValTyped w16 go.uint16.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint8 : IntoValTyped w8 go.uint8.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_uint : IntoValTyped w64 go.uint.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_int64 : IntoValTyped w64 go.int64.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_int32 : IntoValTyped w32 go.int32.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_int16 : IntoValTyped w16 go.int16.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_int8 : IntoValTyped w8 go.int8.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_int : IntoValTyped w64 go.int.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_bool : IntoValTyped bool go.bool.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_string : IntoValTyped go_string go.string.
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_Pointer : IntoValTyped loc unsafe.Pointer.
Proof. solve_into_val_typed. Qed.

End into_val_typed_instances.
