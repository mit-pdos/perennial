From Perennial.goose_lang Require Export lifting proofmode.
From New.golang.defn Require Export exception.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_execute_val (v1 : val) (v : val) :
  PureWp True (exception_seq v1 (execute_val v)) (v1 #()).
Proof.
  rewrite exception_seq_unseal execute_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.

Global Instance pure_do_execute_val (v : val) : PureWp True (do: v) (execute_val v).
Proof.
  rewrite do_execute_unseal execute_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.

Global Instance pure_return_val (v1 : val) (v : val) :
  PureWp True (exception_seq v1 (return_val v)) (return_val v).
Proof.
  rewrite exception_seq_unseal return_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.

Global Instance pure_do_return_val (v : val) : PureWp True (return: v) (return_val v).
Proof.
  rewrite do_return_unseal return_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.

Global Instance pure_exception_do_return_v (v : val) : PureWp True (exception_do (return_val v)%E) (v).
Proof.
  rewrite exception_do_unseal return_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.

Global Instance pure_exception_do_execute_v (v : val) :
  PureWp True (exception_do (execute_val v)%E) (v).
Proof.
  rewrite exception_do_unseal execute_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_rec. wp_pures. iFrame.
Qed.
End wps.
