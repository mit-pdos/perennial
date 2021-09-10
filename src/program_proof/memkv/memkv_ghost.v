From Perennial.Helpers Require Export range_set.
From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude std_proof.
From Perennial.program_proof.memkv Require Export common_proof.

Local Definition kvMapUR := gmapUR u64 (prodR (fracR) (agreeR (leibnizO (list u8))) ).

Class kvMapG Σ :=
  { kv_map_inG :> inG Σ kvMapUR;
    kvMapG_multipar :> multiparG Σ }.

Definition kvMapΣ := #[GFunctor kvMapUR; multiparΣ].

Global Instance subG_kvMapG {Σ} :
  subG (kvMapΣ) Σ → kvMapG Σ.
Proof. solve_inG. Qed.

Definition kvptsto_frac `{!kvMapG Σ} γ (k:u64) (q:Qp) (v:list u8) :=
  own γ {[ k := ((q / 2)%Qp, to_agree (v: leibnizO (list u8))) ]}.

Definition kvptsto `{!kvMapG Σ} γ k v := kvptsto_frac γ k 1%Qp v.

Section memkv_ghost.

Context `{!kvMapG Σ}.

Lemma kvptsto_agree γ k q v q' v':
  kvptsto_frac γ k q v -∗
  kvptsto_frac γ k q' v' -∗
  ⌜v = v'⌝
.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %H. iPureIntro. move: H.
  rewrite singleton_op singleton_valid -pair_op pair_valid.
  intros [_ ?%to_agree_op_inv_L]. done.
Qed.

Lemma kvptsto_update v' γ k v1 v2 :
  kvptsto γ k v1 -∗
  kvptsto γ k v2 ==∗
  kvptsto γ k v' ∗
  kvptsto γ k v'
.
Proof.
  iIntros "H1 H2". rewrite /kvptsto -own_op.
  iApply (own_update_2 with "H1 H2").
  rewrite !singleton_op. apply singleton_update.
  rewrite -!pair_op. rewrite frac_op Qp_half_half.
  apply cmra_update_exclusive.
  rewrite pair_valid to_agree_op_valid_L. done.
Qed.

Definition own_shard γkv sid (m:gmap u64 (list u8)) : iProp Σ :=
  [∗ set] k ∈ (fin_to_set u64), ⌜shardOfC k ≠ sid⌝ ∨
                                kvptsto γkv k (default [] (m !! k))
.

Lemma kvptsto_init n :
  (* iMod on this lemma seems to compute things, so make n "opaque". *)
  n = uNSHARD →
  ⊢ |==> ∃ γ, ([∗ set] sid ∈ rangeSet 0 n, own_shard γ sid ∅) ∗
              ([∗ set] k ∈ fin_to_set u64, kvptsto γ k []).
Proof.
  intros ->.
  pose (m := gset_to_gmap (1%Qp, to_agree []) (fin_to_set u64) : kvMapUR).
  iMod (own_alloc m) as (γ) "Hown".
  { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
    rewrite Some_valid. done. }
  iExists γ. iModIntro.
  iAssert ([∗ set] k ∈ fin_to_set u64, kvptsto γ k [] ∗ kvptsto γ k [])%I with "[Hown]" as "Hown".
  { rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace (fin_to_set u64) with (dom (gset _) m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!#" (k x). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ [= <-]]).
    iIntros "[H1 H2]".
    iFrame. }
  rewrite big_sepS_sep.
  iDestruct "Hown" as "[Hown $]".
  rewrite /own_shard.
  iApply big_sepS_sepS.
  iApply (big_sepS_impl with "Hown").
  iIntros "!#" (k _) "Hown".
  rewrite (big_sepS_delete _ _ (shardOfC k)); last first.
  { apply rangeSet_lookup; first done.
    - compute_done.
    - split; first word.
      specialize (shardOfC_bound k). word. }
  iSplitL.
  - iRight. rewrite lookup_empty. done.
  - iApply big_sepS_intro.
    iIntros "!#" (shard [Hshard Hne]%elem_of_difference). iLeft.
    iPureIntro. intros Heq. apply Hne.
    apply elem_of_singleton. done.
Qed.

End memkv_ghost.
