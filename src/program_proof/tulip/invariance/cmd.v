From Perennial.program_proof.tulip Require Import prelude.

Section lemma.
  Context `{!tulip_ghostG Σ}.

  Lemma repl_hist_multiwrite_disjoint {γ} ts wrs hists :
    dom hists ## dom wrs ->
    ([∗ map] k ↦ hist ∈ hists, own_repl_hist_half γ k hist) -∗
    ([∗ map] k ↦ hist ∈ multiwrite ts wrs hists, own_repl_hist_half γ k hist).
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply multiwrite_dom.
    iIntros "!>" (k h1 h2 Hh1 Hh2) "Hhist".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Hh1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /multiwrite lookup_merge Hwrs Hh1 /= in Hh2.
    by inv Hh2.
  Qed.

  Lemma repl_ts_release_disjoint {γ} wrs ptsm :
    dom ptsm ## dom wrs ->
    ([∗ map] k ↦ pts ∈ ptsm, own_repl_ts_half γ k pts) -∗
    ([∗ map] k ↦ pts ∈ release wrs ptsm, own_repl_ts_half γ k pts).
  Proof.
    iIntros (Hdom) "Hptsm".
    iApply (big_sepM_impl_dom_eq with "Hptsm"); first apply release_dom.
    iIntros "!>" (k t1 t2 Ht1 Ht2) "Hpts".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Ht1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /release lookup_merge Hwrs Ht1 /= in Ht2.
    by inv Ht2.
  Qed.

End lemma.
