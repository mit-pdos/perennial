From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing pure_proofmode.
From New.golang.defn Require Import interface.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp__interface_get (i : interface.t) (method : string) :
  PureWp (True) (interface.get method #i)
    (match (assocl_lookup method i.(interface.mset)) with
     | None => (App #() i.(interface.v))
     | Some m => (App m i.(interface.v))
     end).
Proof.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call.
  destruct assocl_lookup; wp_pures; rewrite ?to_val_unseal //=.
Qed.

Global Instance wp_interface_make (v : val) (mset : list (string * val)) :
  PureWp (True) (interface.make mset v) #(interface.mk v mset).
Proof.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal interface.make_unseal.
  wp_call. done.
Qed.

End wps.
