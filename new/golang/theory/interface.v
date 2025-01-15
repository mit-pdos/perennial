From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing proofmode globals.
From New.golang.defn Require Import interface globals.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) pkg_name type_name :
  PureWp (i.(interface.opt_pkg_type_name) = Some (pkg_name, type_name))
    (interface.get #method #i)
    (method_call #pkg_name #type_name #method i.(interface.v)).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #i]to_val_unseal.
  wp_call_lc "?". rewrite H.
  wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) pkg_name type_name :
  PureWp (True) (interface.make #pkg_name #type_name v) #(interface.mk v (Some (pkg_name, type_name))).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #(_ : interface.t)]to_val_unseal interface.make_unseal.
  wp_call_lc "?". wp_pures. by iApply "Hwp".
Qed.

End wps.
