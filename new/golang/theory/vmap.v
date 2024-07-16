From Perennial.goose_lang Require Import proofmode lifting.
From New.golang.defn Require Export vmap.
From New.golang.theory Require Import list.
From stdpp Require Import sorting.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Local Instance cmp_trans : Transitive vmap.vmap.cmp.
Proof.
  intros [][][]??. simpl in *.
  unfold is_true in *. rewrite !Pos.leb_le in H H0 *. lia.
Qed.

Local Instance cmp_total : Total vmap.vmap.cmp.
Proof.
  intros [][]. simpl in *.
  unfold is_true in *. rewrite !Pos.leb_le. lia.
Qed.

Search map_to_list.

Local Lemma Sorted_unique l1 l2 :
  NoDup l1.*1 →
  NoDup l2.*1 →
  Sorted (vmap.vmap.cmp) l1 →
  Sorted (vmap.vmap.cmp) l2 →
  l1 ≡ₚ l2 →
  l1 = l2.
Proof.
Admitted.

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
    rewrite /vmap.val_def /vmap.vmap.val_list_def insert_empty map_to_list_singleton /=.
    by iApply "HΦ".
  - iIntros (?) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_list_Match).
    wp_pures.
    set (l:=vmap.vmap.val_list_def (_)).
    destruct l eqn:Hl.
    { exfalso. subst l.
      rewrite /vmap.vmap.val_list_def /= in Hl.
      apply fmap_nil_inv, (f_equal length) in Hl.
      erewrite (Permutation_length ltac:(eapply merge_sort_Permutation)) in Hl.
      by rewrite map_to_list_length map_size_insert H /= in Hl.
    }
    wp_pures.
    subst l.
    rewrite /vmap.val_list_def /= in Hl.
    apply fmap_cons_inv in Hl as [[] [? [-> [ -> Hl]]]]. subst.
    wp_pures.
    wp_if_destruct.
    {
      wp_pures.
      wp_if_destruct.
      - apply Pos.leb_le in Heqb, Heqb0.
        pose proof (Pos.le_antisym _ _ Heqb Heqb0) as Heq.
        clear Heqb Heqb0.
        apply (f_equal (decode (A:=val))) in Heq.
        rewrite !decode_encode in Heq. injection Heq as ->.
        wp_pures.
        iModIntro.
        iSpecialize ("HΦ" with "[//]").
        iExactEq "HΦ".
        rewrite /vmap.val_def /=.
        repeat f_equal.
        rewrite /vmap.val_list_def /=.
        change (v1, v)%V with ((λ x2 : val * val, let (a, b) := x2 in (a, b)%V) (v1, v)).
        rewrite -fmap_cons. f_equal.
        apply Sorted_unique.
        { setoid_rewrite (merge_sort_Permutation). apply NoDup_fst_map_to_list. }
        {
          change (NoDup ((v1, v) :: x1).*1) with (NoDup ((v1, v2) :: x1).*1).
          rewrite -Hl. setoid_rewrite (merge_sort_Permutation). apply NoDup_fst_map_to_list. }
        { apply Sorted_merge_sort. apply _. }
        {
          lazymatch goal with [ H : merge_sort ?c ?l = ?l2 |- _ ] =>
                                (pose proof Sorted_merge_sort (H:=(@vmap.cmp_dec ext)) c l) end.
          rewrite Hl in H0.
          inversion H0. subst.
          econstructor.
          { done. }
          { inversion H4; econstructor. done. }
        }
        {
          lazymatch goal with [ H : merge_sort ?c ?l = ?l2 |- _ ] =>
                                (pose proof Sorted_merge_sort (H:=(@vmap.cmp_dec ext)) c l as Hs) end.
          rewrite Hl in Hs.
          setoid_rewrite merge_sort_Permutation.

        }
    }

Admitted.

End wps.
