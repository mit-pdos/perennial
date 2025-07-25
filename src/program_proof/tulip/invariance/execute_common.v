From Perennial.program_proof.tulip Require Import prelude.

Lemma prepared_impl_locked_inv_release cpm ptsm ts pwrs :
  cpm !! ts = Some pwrs ->
  prepared_impl_locked_cpm cpm ptsm ->
  prepared_impl_locked_cpm (delete ts cpm) (release pwrs ptsm).
Proof.
  intros Hpwrs Hpil t w k Hw Hk.
  destruct (decide (t = ts)) as [-> | Hne]; first by rewrite lookup_delete_eq in Hw.
  rewrite lookup_delete_ne in Hw; last done.
  rewrite release_unmodified; last first.
  { apply not_elem_of_dom.
    pose proof (prepared_impl_locked_disjoint _ _ _ _ _ _ Hne Hw Hpwrs Hpil) as Hdisj.
    set_solver.
  }
  by specialize (Hpil _ _ _ Hw Hk).
Qed.
