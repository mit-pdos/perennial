From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing proofmode.
From New.golang.defn Require Import interface globals.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) :
  PureWp (True) (interface.get method #i)
         (method_call i.(interface.pkg_type_name) method i.(interface.v)).

    (match (assocl_lookup method i.(interface.mset)) with
     | None => (App #() i.(interface.v))
     | Some m => (App m i.(interface.v))
     end).
Proof.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call_lc "?".
  destruct assocl_lookup; wp_pures; rewrite ?to_val_unseal /=; by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) (mset : list (go_string * val)) :
  PureWp (True) (interface.make mset v) #(interface.mk v mset).
Proof.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal interface.make_unseal.
  wp_call_lc "?". by iApply "Hwp".
Qed.

End wps.
