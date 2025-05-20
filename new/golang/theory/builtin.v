From New Require Export notation.
From New.golang.defn Require Export builtin.
From New.golang.theory Require Import typing proofmode.
From Perennial Require Import base.

Module error.
  Section def.
  Context `{ffi_syntax}.
  Definition t := interface.t.
  End def.
End error.

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_int64_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Global Instance wp_int64_lt (l r : w64) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_gt (l r : w32) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_lt (l r : w32) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. Admitted.

Global Instance wp_int64_geq (l r : w64) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. Admitted.

Global Instance wp_int64_leq (l r : w64) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_geq (l r : w32) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_leq (l r : w32) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. Admitted.

End wps.
