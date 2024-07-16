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
      rewrite /map_fold /gmap_fold /= in Hl.
      rewrite map_fold_insert_L in Hl; last done.
      {
        apply (f_equal length) in Hl.
        rewrite /vmap.insert_replace_sorted /= in Hl.
        set y:=(map_fold _ _ _) in Hl.
        destruct y.
        { done. }
        { destruct p, (val_le i v0), (val_le v0 i); done. }
      }
      intros.
      induction y.
      {
        simpl. destruct (val_le j1 j2) eqn:Hy, (val_le j2 j1) eqn:Hx.
        - exfalso. unfold val_le in *.
          rewrite !Pos.leb_le in Hx, Hy.
          pose proof (Pos.le_antisym _ _ Hx Hy).
          apply (f_equal (decode (A:=val))) in H3.
          rewrite !decode_encode in H3.
          inversion H3. subst. done.
        - done.
        - done.
        - exfalso.
          rewrite !Positive_as_OT.leb_nle in Hx Hy.
          pose proof (Pos.le_total (encode j1) (encode j2)) as [|].
          + by apply Hx.
          + by apply Hy.
      }
      {
        destruct a. simpl in *.
        destruct (val_le j1 j2) eqn:Hy, (val_le j2 j1) eqn:Hx,
                   (val_le j1 v0) eqn:?, (val_le j2 v0) eqn:?,
                     (val_le v0 j1) eqn:?, (val_le v0 j2) eqn:?;
        unfold val_le in *; simpl in *;
          repeat lazymatch goal with
          | [ H : context [Pos.leb] |- _ ] => rewrite ?H; rewrite ?Pos.leb_le ?Pos.leb_gt in H
          end;
          repeat lazymatch goal with
            | [ H1 : Pos.le ?a ?b , H2 : Pos.le ?b ?a |- _ ] =>
                let Htmp := fresh in
                pose proof (Pos.le_antisym _ _ H1 H2) as Htmp; clear H1 H2;
                apply (f_equal (decode (A:=val))) in Htmp;
                rewrite !decode_encode in Htmp; injection Htmp as ->
            end.
        all: try (reflexivity || lia || by exfalso).
      }
    }
    admit.
Admitted.

End wps.
