From New.golang.defn Require Export builtin.
From New.golang.theory Require Export proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Module error.
  Section def.
  Context `{ffi_syntax}.
  Definition t := interface.t.
  End def.
End error.

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_int64_lt (l r : w64) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int64_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.
Global Instance wp_int64_leq (l r : w64) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int64_geq (l r : w64) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.

Global Instance wp_int32_lt (l r : w32) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int32_gt (l r : w32) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.
Global Instance wp_int32_leq (l r : w32) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int32_geq (l r : w32) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.

Global Instance wp_int16_lt (l r : w16) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int16_gt (l r : w16) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.
Global Instance wp_int16_leq (l r : w16) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int16_geq (l r : w16) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.

Global Instance wp_int8_lt (l r : w8) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int8_gt (l r : w8) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.
Global Instance wp_int8_leq (l r : w8) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. by pure_wp_start. Qed.
Global Instance wp_int8_geq (l r : w8) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. pure_wp_start. repeat case_bool_decide; (done || lia). Qed.

Lemma wp_make_nondet_uint64 (v : val) :
  {{{ True }}}
    make_nondet go.uint64 v
  {{{ (x : w64), RET #x; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_call. rewrite decide_True //. wp_apply wp_ArbitraryInt.
  rewrite to_val_unseal //.
Qed.

(*
Lemma wp_make_nondet_float64 (v : val) :
  {{{ True }}}
    make_nondet go.float64T v
  {{{ (x : w64), RET #x; True }}}.
Proof.
  apply wp_make_nondet_uint64.
Qed.

Lemma wp_make_nondet_uint32 (v : val) :
  {{{ True }}}
    make_nondet uint32T v
  {{{ (x : w32), RET #x; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_call. wp_apply wp_ArbitraryInt. iIntros (?) "_".
  replace (LitV x) with #x.
  2:{ rewrite to_val_unseal //. }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_make_nondet_float32 (v : val) :
  {{{ True }}}
    make_nondet float32T v
  {{{ (x : w32), RET #x; True }}}.
Proof.
  apply wp_make_nondet_uint32.
Qed. *)

End wps.

#[global] Opaque int_lt int_leq int_gt int_geq make_nondet.
