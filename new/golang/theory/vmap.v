From Perennial.goose_lang Require Import proofmode lifting.
From New.golang.defn Require Export vmap.
From New.golang.theory Require Import list.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* XXX: this is a "pure" step. *)
Lemma wp_vmap_Insert (k v : val) (m : gmap val val) :
  {{{ True }}}
    vmap.Insert k v (vmap.val m)
  {{{ RET (vmap.val (<[k := v]> m)); True }}}.
Proof.
  iInduction m as [] "IH" using map_ind; rewrite vmap.val_unseal.
  - (* empty map *)
    iIntros (?) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_list_Match).
    wp_pures.
    rewrite /vmap.val_def /vmap.vmap.val_list_def insert_empty map_fold_singleton /=.
    by iApply "HΦ".
  - iIntros (?) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_list_Match).
    wp_pures.
    set (l:=vmap.vmap.val_list_def (_)).
    destruct l eqn:Hl.
    { exfalso. subst l.
      rewrite /vmap.vmap.val_list_def /= in Hl.
      apply fmap_nil_inv in Hl.
      Require Import Coq.Program.Equality.
      revert Hl.
      pattern (<[i:=x]> m).
      pattern (map_fold
(λ (k0 v0 : val) (kvs : list (val * val)),
       vmap.insert_replace_sorted (λ '(a, _) '(b, _), val_le a b) (k0, v0) kvs)
                 [] (<[i:=x]> m)).
      set P:=
        (λ g : gmap val val,
           (λ l : list (val * val), l = [] → False)
             (map_fold
                (λ (k0 v0 : val) (kvs : list (val * val)),
                   vmap.insert_replace_sorted (λ '(a, _) '(b, _), val_le a b) (k0, v0) kvs) [] g)).
      apply (map_fold_ind (K:=val) (A:=val) (B:=list (val * val)) P).

      set P:=(λ l m, l = [] → False).
      (λ '(a, b), (a, b)%V) <$>
        map_fold
        (λ (k0 v0 : val) (kvs : list (val * val)),
           vmap.insert_replace_sorted (λ '(a, _) '(b, _), val_le a b) (k0, v0) kvs) []
        (<[i:=x]> m) = [] → False

      pattern (map_fold
(λ (k0 v0 : val) (kvs : list (val * val)),
       vmap.insert_replace_sorted (λ '(a, _) '(b, _), val_le a b) (k0, v0) kvs)
                 [] (<[i:=x]> m)).
      pattern m.
      apply (map_fold_ind (K:=val) (A:=val) (B:=list (val * val))).
      set (f:=(map_fold _ [] (<[i:=x]> m))) in Hl.
      About map_fold_ind.
      induction f using map_fold_ind.
      unfold map_fold in Hl.
      Search gmap_fold.

Qed.

End wps.
