From Perennial.goose_lang Require Import notation proofmode.
From New.golang.theory Require Import struct typing.
From New.golang.defn Require Import interface.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp__interface_get (v : val) (mset : list (string * val)) (method : string) :
  PureWp (True) (interface.get method (interface.val mset v))
    (match (assocl_lookup method mset) with | None => (App #() v) | Some m => (App m v) end).
Proof.
  iIntros (?????) "Hwp".
  rewrite interface.val_unseal.
  wp_rec. wp_pures.
  destruct (assocl_lookup method mset); wp_pures; done.
Qed.

Global Instance wp_interface_make (v : val) (mset : list (string * val)) :
  PureWp (True) (interface.make mset v) (interface.val mset v).
Proof.
  iIntros (?????) "Hwp".
  rewrite interface.val_unseal interface.make_unseal.
  wp_rec. wp_pures. done.
Qed.

End wps.
