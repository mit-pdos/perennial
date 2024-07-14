From Perennial.goose_lang Require Import proofmode lifting.
From New.golang.defn Require Export vmap.
From New.golang.theory Require Import list.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* XXX: this is a "pure" step. *)
Lemma wp_vmap_Insert (k v : val) (m : gmap val val) :
  {{{ True }}}
    vmap.Insert k v (vmap.val m)
  {{{ RET (vmap.val (<[k := v]> m)); True }}}
.
Proof.
  iIntros (?) "_ HΦ".
  rewrite vmap.val_unseal /vmap.Insert.
  wp_pures.
  rewrite /vmap.val_def.
  iApply "HΦ".
Qed.

End wps.
