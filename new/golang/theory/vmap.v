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
  assert (∃ l, vmap.val_list_def m = l) as [l Hl].
  { eexists _. done. }
  iInduction l as [] "IH" forall (m Hl); rewrite vmap.val_unseal.
  - (* empty map *)
    iIntros (?) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_list_Match).

    rewrite /vmap.val_def /vmap.vmap.val_list_def /= in Hl.
    apply fmap_nil_inv, Permutation_nil_r in Hl.
    rewrite merge_sort_Permutation in Hl.
    apply Permutation_nil_r, (f_equal length) in Hl.
    rewrite map_to_list_length /= in Hl.
    rewrite map_size_empty_iff in Hl. subst.
    rewrite /vmap.val_def /vmap.vmap.val_list_def map_to_list_empty
      insert_empty map_to_list_singleton /=.

    wp_pures.
    by iApply "HΦ".
  - iIntros (?) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_list_Match).
    rewrite Hl.
    rewrite /vmap.val_def /vmap.vmap.val_list_def /= in Hl.
    apply fmap_cons_inv in Hl as [[k' v'] [? [-> [-> Hl]]]].
    wp_pures.
    wp_if_destruct.
    {
      wp_pures.
      wp_if_destruct.
      - apply Pos.leb_le in Heqb, Heqb0.
        pose proof (Pos.le_antisym _ _ Heqb Heqb0) as Heq.
        clear Heqb Heqb0.
        apply (f_equal (decode (A:=val))) in Heq.
        rewrite !decode_encode in Heq. injection Heq as <-.
        wp_pures.
        iModIntro.
        iSpecialize ("HΦ" with "[//]").
        iExactEq "HΦ".
        rewrite /vmap.val_def /=.
        repeat f_equal.
        rewrite /vmap.val_list_def /=.
        change (k, v)%V with ((λ x2 : val * val, let (a, b) := x2 in (a, b)%V) (k, v)).
        rewrite -fmap_cons. f_equal.
        apply Sorted_unique.
        { setoid_rewrite (merge_sort_Permutation). apply NoDup_fst_map_to_list. }
        {
          change (NoDup ((k, v) :: x0).*1) with (NoDup ((k, v') :: x0).*1).
          rewrite -Hl. setoid_rewrite (merge_sort_Permutation). apply NoDup_fst_map_to_list. }
        { apply Sorted_merge_sort. apply _. }
        {
          lazymatch goal with [ H : merge_sort ?c ?l = ?l2 |- _ ] =>
                                (pose proof Sorted_merge_sort (H:=(@vmap.cmp_dec ext)) c l) end.
          rewrite Hl in H. inversion H; inversion H3; subst;
          econstructor; try done; econstructor; done.
        }
        {
          apply (reflexive_eq_dom_reflexive (R':=(≡ₚ)) id) in Hl.
          rewrite /= !merge_sort_Permutation in Hl |- *.
          assert (m = (insert k v' (delete k m))).
          {
            symmetry. apply insert_delete.
            apply elem_of_map_to_list.
            rewrite Hl.
            constructor.
          }
          rewrite H in Hl |- *.
          rewrite insert_insert.
          rewrite !map_to_list_insert in Hl |- *; try by apply lookup_delete.
          apply Permutation_cons_inv in Hl. naive_solver.
        }
      - admit.
    }
    admit.
Admitted.

End wps.
