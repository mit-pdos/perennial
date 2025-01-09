From iris.algebra.lib Require Import dfrac_agree.
From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!tulip_ghostG Σ}.

  Definition own_phys_hist_half α (key : byte_string) (hist : dbhist) : iProp Σ :=
    own α {[ key := (to_dfrac_agree (DfracOwn (1 / 2)) hist) ]}.

  Lemma phys_hist_update {α k h1 h2} h :
    own_phys_hist_half α k h1 -∗
    own_phys_hist_half α k h2 ==∗
    own_phys_hist_half α k h ∗
    own_phys_hist_half α k h.
  Proof.
    iIntros "Hv1 Hv2".
    iCombine "Hv1 Hv2" as "Hv".
    rewrite -own_op singleton_op.
    iApply (own_update with "Hv").
    apply singleton_update.
    apply dfrac_agree_update_2.
    by rewrite dfrac_op_own Qp.half_half.
  Qed.

  Lemma phys_hist_agree α k h1 h2 :
    own_phys_hist_half α k h1 -∗
    own_phys_hist_half α k h2 -∗
    ⌜h2 = h1⌝.
  Proof.
    iIntros "Hv1 Hv2".
    iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
    rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
    by destruct Hvalid as [_ ?].
  Qed.

  Lemma phys_hist_alloc :
    ⊢ |==> ∃ α, ([∗ set] k ∈ keys_all, own_phys_hist_half α k [None]) ∗
                ([∗ set] k ∈ keys_all, own_phys_hist_half α k [None]).
  Proof.
    set m : gmap dbkey (dfrac_agreeR dbhistO) :=
      gset_to_gmap (to_dfrac_agree (DfracOwn 1) [None : dbval]) keys_all.
    iMod (own_alloc m) as (α) "Htpls".
    { intros k.
      rewrite /m.
      rewrite lookup_gset_to_gmap.
      destruct (decide (k ∈ keys_all)).
      - rewrite option_guard_True //.
      - rewrite option_guard_False //.
    }
    iExists α.
    rewrite /m. rewrite /own_phys_hist_half.
    rewrite -big_sepS_sep.
    setoid_rewrite <-own_op.
    setoid_rewrite singleton_op.
    setoid_rewrite <-dfrac_agree_op.
    setoid_rewrite dfrac_op_own.
    rewrite -big_opS_own_1 Qp.half_half big_opS_gset_to_gmap //.
  Qed.

End res.
