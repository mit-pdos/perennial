From New Require Import ghost.
From Perennial.Helpers Require Export ipm NamedProps.

Set Default Proof Using "Type".

Section auth_prop.

Context `{!allG Σ}.

Definition own_aprop_auth γ (P : iProp Σ) (n : nat) : iProp Σ :=
  ∃ gns,
    "Hgns" ∷ ghost_map_auth γ 1 (gset_to_gmap () gns) ∗
    "#Hused" ∷ ([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q) ∗
    "#HimpliesP" ∷ □(([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q ∗ ▷ Q) ∗-∗ ▷ P) ∗
    "%Hn" ∷ ⌜ size gns = n ⌝.
#[global] Opaque own_aprop_auth.
#[local] Transparent own_aprop_auth.

Definition own_aprop_frag γ (P : iProp Σ) (n : nat) : iProp Σ :=
  ∃ gns,
    "Hgns" ∷ ([∗ set] γprop ∈ gns, γprop ↪[γ] ()) ∗
    "#HimpliesP" ∷ □(([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q ∗ ▷ Q) ∗-∗ ▷ P) ∗
    "%Hn" ∷ ⌜ size gns = n ⌝.
#[global] Opaque own_aprop_frag.
#[local] Transparent own_aprop_frag.

Notation own_aprop γ P := (own_aprop_frag γ P 1).

Lemma own_aprop_auth_alloc :
  ⊢ |==> ∃ γ, own_aprop_auth γ True 0.
Proof.
  iMod (ghost_map_alloc (∅ : gmap gname unit)) as (γ) "[H _]".
  iExists γ. unfold own_aprop_auth. iExists ∅.
  rewrite gset_to_gmap_empty. iFrame. rewrite !big_sepS_empty //.
  iModIntro. repeat iSplitL; try done. iModIntro. iIntros "_ "; done.
Qed.

Lemma own_aprop_auth_add Q γ P n :
  ⊢ own_aprop_auth γ P n ==∗ own_aprop_auth γ (P ∗ Q) (S n) ∗ own_aprop γ Q.
Proof.
  iNamed 1.
  iMod (saved_prop_alloc Q (DfracOwn 1)) as (γprop) "HQ"; first done.
  destruct (decide (γprop ∈ gns)).
  { iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hused") as "[[% Hbad] _]"; first done.
    iCombine "Hbad HQ" gives "[%Hbad _]". done. }
  iMod (ghost_map_insert γprop () with "Hgns") as "[Hgns_auth Hgns']".
  { rewrite lookup_gset_to_gmap_None //. }
  rewrite -gset_to_gmap_union_singleton.
  iMod (saved_prop_persist with "HQ") as "#HQ".
  iModIntro. iSplitR "Hgns'".
  { iFrame. assert ({[γprop]} ## gns) by set_solver.
    repeat rewrite !big_sepS_union // !big_sepS_singleton. iFrame "∗#".
    subst. rewrite size_union // size_singleton /=. iSplitL; last done. iModIntro.
    iSplit.
    - iIntros "[HQ' HPs]". iSpecialize ("HimpliesP" with "HPs"). iFrame.
      iDestruct "HQ'" as (?) "[HQ' HQfact]". iCombine "HQ HQ'" gives "[_ H]".
      iNext. iRewrite "H". iFrame.
    - iIntros "[HPfact HQfact]". iSplitR "HPfact HimpliesP".
      + iExists _; iFrame "#∗".
      + by iApply "HimpliesP".
  }
  iExists {[ _ ]}. rewrite !big_sepS_singleton. iFrame. rewrite size_singleton.
  iSplitL; last done. iModIntro. iSplit.
  - iIntros "(% & HQ' & HQfact)". iCombine "HQ HQ'" gives "[_ Heq]".
    iNext. iRewrite "Heq". iFrame.
  - iIntros "?". iFrame "#∗".
Qed.

Lemma own_aprop_auth_reset γ P P' n :
  ⊢ own_aprop_auth γ P n -∗ own_aprop_frag γ P' n ==∗ own_aprop_auth γ True O.
Proof.
  iNamed 1. iNamedSuffix 1 "'".
  iDestruct (ghost_map_lookup_big with "Hgns [Hgns']") as "%Hsub".
  { instantiate (1:=gset_to_gmap () gns0). rewrite big_sepM_gset_to_gmap. iFrame. }
  apply subseteq_dom in Hsub. rewrite !dom_gset_to_gmap in Hsub.
  apply set_subseteq_size_eq in Hsub as Heq; last lia. subst.
  iMod (ghost_map_delete_big with "Hgns [Hgns']") as "Hgns".
  { instantiate (1:=gset_to_gmap () gns). rewrite big_sepM_gset_to_gmap. iFrame. }
  rewrite map_difference_diag.
  iModIntro. iExists ∅. rewrite gset_to_gmap_empty. iFrame.
  rewrite !big_sepS_empty.
  repeat iSplitL; try done. iModIntro. iIntros "_ "; done.
Qed.

Lemma own_aprop_frag_0 γ :
  ⊢ own_aprop_frag γ True 0.
Proof.
  iExists ∅. rewrite !big_sepS_empty. repeat iSplitL; try done.
  iModIntro. by iIntros.
Qed.

#[global] Instance own_aprop_auth_agree γ P P' n :
  CombineSepGives (own_aprop_auth γ P n) (own_aprop_frag γ P' n) (▷ P ∗-∗ ▷ P').
Proof.
  rewrite /CombineSepGives. iIntros "[@ H]". iNamedSuffix "H" "'".
  iDestruct (ghost_map_lookup_big with "Hgns [Hgns']") as "%Hsub".
  { instantiate (1:=gset_to_gmap () gns0). rewrite big_sepM_gset_to_gmap. iFrame. }
  apply subseteq_dom in Hsub. rewrite !dom_gset_to_gmap in Hsub.
  apply set_subseteq_size_eq in Hsub as Heq; last lia. subst. clear Hn' Hsub.
  iModIntro.
  iSplit.
  - iIntros "HP". iApply "HimpliesP" in "HP". iApply "HimpliesP'" in "HP". iFrame.
  - iIntros "HP'". iApply "HimpliesP'" in "HP'". iApply "HimpliesP" in "HP'". iFrame.
Qed.

#[global] Instance own_aprop_auth_agree' γ P P' n :
  CombineSepGives (own_aprop_frag γ P' n) (own_aprop_auth γ P n)  (▷ P' ∗-∗ ▷ P).
Proof.
  rewrite /CombineSepGives. iIntros "[H H']". iCombine "H' H" gives "[? ?]". iModIntro.
  iSplit; done.
Qed.

(* higher cost to prefer [own_aprop_auth_agree]. *)
#[global] Instance own_aprop_auth_le γ P P' n n' :
  CombineSepGives (own_aprop_auth γ P n) (own_aprop_frag γ P' n') (⌜ n' ≤ n ⌝)%I | 10.
Proof.
  rewrite /CombineSepGives. iIntros "[@ H]". iNamedSuffix "H" "'".
  iDestruct (ghost_map_lookup_big with "Hgns [Hgns']") as "%Hsub".
  { instantiate (1:=gset_to_gmap () gns0). rewrite big_sepM_gset_to_gmap. iFrame. }
  apply subseteq_dom in Hsub. rewrite !dom_gset_to_gmap in Hsub.
  iModIntro. iPureIntro. apply subseteq_size in Hsub. lia.
Qed.

#[global] Instance own_aprop_auth_le' γ P P' n n' :
  CombineSepGives (own_aprop_frag γ P' n') (own_aprop_auth γ P n) (⌜ n' ≤ n ⌝)%I | 10.
Proof.
  rewrite /CombineSepGives. iIntros "[H H']". iCombine "H' H" gives %H. iModIntro. done.
Qed.

#[global] Instance own_aprop_frag_combine γ P P' n n' :
  CombineSepAs (own_aprop_frag γ P n) (own_aprop_frag γ P' n') (own_aprop_frag γ (P ∗ P') (n + n')).
Proof.
  rewrite /CombineSepAs. iIntros "[@ H]". iNamedSuffix "H" "'". rename gns0 into gns'.
  destruct (decide (gns ∩ gns' = ∅)) as [Hdisj|Hbad].
  2:{
    apply set_choose_L in Hbad. destruct Hbad as [γprop Hbad].
    iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hgns") as "[H1 _]";
      first set_solver.
    iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hgns'") as "[H2 _]";
      first set_solver.
    iCombine "H1 H2" gives %[Hbad' _]. done.
  }
  apply disjoint_intersection_L in Hdisj.
  iExists (gns ∪ gns'). rewrite big_sepS_union //. iFrame.
  rewrite big_sepS_union //. rewrite size_union //.
  iSplitL; last (iPureIntro; lia). iModIntro. iSplit.
  - iIntros "[H H']". iApply "HimpliesP" in "H". iApply "HimpliesP'" in "H'". iFrame.
  - iIntros "[H H']". iApply "HimpliesP" in "H". iApply "HimpliesP'" in "H'". iFrame.
Qed.

End auth_prop.
#[global] Notation own_aprop γ P := (own_aprop_frag γ P 1).
