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
Existing Class go.is_predeclared_zero_val.
#[local] Hint Extern 1 (go.is_predeclared_zero_val ?t ?v) => constructor : typeclass_instances.

Local Set Default Proof Using "Type core_sem pre_sem".
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

End into_val_typed_instances.

Section inequality_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}.

Ltac solve_eq lem :=
  constructor; rewrite lem; iIntros "* ?"; by wp_pures.

Ltac solve_ineq lem :=
  iIntros (?) "* _ * HΦ";
  iApply wp_GoInstruction; [intros; repeat econstructor|];
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure;
  iIntros "? $ !>"; rewrite lem; iApply "HΦ"; iFrame.

Global Instance is_go_eq_uint (v1 v2 : w64) :
  IsGoEq go.uint #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_uint. Qed.
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

Global Instance is_go_eq_uint64 (v1 v2 : w64) :
  IsGoEq go.uint64 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_uint64. Qed.
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

Global Instance is_go_eq_uint32 (v1 v2 : w32) :
  IsGoEq go.uint32 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_uint32. Qed.
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

Global Instance is_go_eq_uint16 (v1 v2 : w16) :
  IsGoEq go.uint16 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_uint16. Qed.
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

Global Instance is_go_eq_uint8 (v1 v2 : w8) :
  IsGoEq go.uint8 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_uint8. Qed.
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

Global Instance is_go_eq_int (v1 v2 : w64) :
  IsGoEq go.int #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_int. Qed.
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

Global Instance is_go_eq_int64 (v1 v2 : w64) :
  IsGoEq go.int64 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_int64. Qed.
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

Global Instance is_go_eq_int32 (v1 v2 : w32) :
  IsGoEq go.int32 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_int32. Qed.
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

Global Instance is_go_eq_int16 (v1 v2 : w16) :
  IsGoEq go.int16 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_int16. Qed.
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

Global Instance is_go_eq_int8 (v1 v2 : w8) :
  IsGoEq go.int8 #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_int8. Qed.
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

Global Instance is_go_eq_string (v1 v2 : go_string) :
  IsGoEq go.string #v1 #v2 (bool_decide (v1 = v2)).
Proof. solve_eq go.go_eq_string. Qed.

End inequality_instances.
