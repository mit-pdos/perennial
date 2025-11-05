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

Ltac pure_wp_start :=
  apply pure_wp_val; intros ????;
  iIntros "HΦ"; try (wp_call_lc "Hlc"; try iSpecialize ("HΦ" with "[$Hlc]")).

Lemma wp_make_nondet_uint64 (v : val) :
  {{{ True }}}
    make_nondet go.uint64 v
  {{{ (x : w64), RET #x; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_call. rewrite decide_True //. wp_apply wp_ArbitraryInt.
  rewrite into_val_unseal //.
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

#[global] Opaque make_nondet.
