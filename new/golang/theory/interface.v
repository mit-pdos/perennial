From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing proofmode globals.
From New.golang.defn Require Import interface globals.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) pkg_name type_name v :
  PureWp (i = interface.mk pkg_name type_name v)
    (interface.get #method #i)
    (#(method_callv pkg_name type_name method v)).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #i]to_val_unseal interface.get_unseal.
  wp_call_lc "?". rewrite H.
  wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) pkg_name type_name :
  PureWp (True) (interface.make #pkg_name #type_name v) #(interface.mk pkg_name type_name v).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #(_ : interface.t)]to_val_unseal interface.make_unseal.
  wp_call_lc "?". wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_eq_nil_r (i : interface.t) :
  PureWp (True) (interface.eq #i #interface.nil) #(bool_decide (i = interface.nil)).
Proof.
  pose proof wp_eq_val.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call_lc "?".
  rewrite to_val_unseal.
  destruct i as [|].
  - wp_pures. wp_pures. rewrite bool_decide_false //. by iApply "Hwp".
  - wp_pures. rewrite bool_decide_true //. by iApply "Hwp".
Qed.

Global Instance wp_interface_eq_nil_l (i : interface.t) :
  PureWp (True) (interface.eq #interface.nil #i) #(bool_decide (interface.nil = i)).
Proof.
  pose proof wp_eq_val.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call_lc "?".
  rewrite to_val_unseal.
  destruct i as [|].
  - wp_pures. wp_pures. rewrite bool_decide_false //. by iApply "Hwp".
  - wp_pures. rewrite bool_decide_true //. by iApply "Hwp".
Qed.

End wps.
