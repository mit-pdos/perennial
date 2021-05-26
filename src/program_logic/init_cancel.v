From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt.
Set Default Proof Using "Type".
Import uPred.

Section modality.
Context `{IRISG: !irisGS Λ Σ}.

Definition init_cancel (P Pc : iProp Σ) : iProp Σ :=
  (∀ e s k Φ Φc Φc' mj (HLT: (/2 < mj)%Qp),
    (P -∗ WPC e @ s; k; ⊤ {{ λ v, wpc_crash_modality ⊤ mj (Pc ∗ Φc') -∗ Φ v }} {{ Pc -∗ Φc }}) -∗
    WPC e @ s; k; ⊤ {{ λ v, wpc_crash_modality ⊤ mj Φc' -∗ Φ v }} {{ Φc }}).

Lemma init_cancel_elim s k e Φ Φc P Pc :
  init_cancel P Pc -∗
  (P -∗ WPC e @ s; k; ⊤ {{ Φ }} {{ Pc -∗ Φc }}) -∗
  WPC e @ s; k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  rewrite /init_cancel. iIntros "H Hwp".
  iAssert (WPC e @ s; k; ⊤ {{ v, wpc_crash_modality ⊤ 1%Qp True%I -∗ Φ v }} {{ Φc }})%I with "[-]" as "H".
  { unshelve (iApply ("H" $! _ _ _ _ _ True%I 1%Qp _)); eauto.
    { rewrite //=. }
    iIntros "HP". iSpecialize ("Hwp" with "[$]").
    iApply (wpc_mono with "Hwp"); eauto. }
  iApply (wpc_mono with "H"); eauto.
  iIntros (?) "H". iApply "H".
  iApply wpc_crash_modality_intro; eauto.
Qed.

Lemma init_cancel_elim' s k e Φ Φc P Pc mj :
  (/2 < mj)%Qp →
  init_cancel P Pc -∗
  (P -∗ WPC e @ s; k; ⊤ {{ λ v, wpc_crash_modality ⊤ mj Pc -∗ Φ v }} {{ Pc -∗ Φc }}) -∗
  WPC e @ s; k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  rewrite /init_cancel. iIntros (?) "H Hwp".
  iAssert (WPC e @ s; k; ⊤ {{ v, wpc_crash_modality ⊤ mj%Qp True%I -∗ Φ v }} {{ Φc }})%I with "[-]" as "H".
  { unshelve (iApply ("H" $! _ _ _ _ _ True%I mj%Qp _)); eauto.
    iIntros "HP". iSpecialize ("Hwp" with "[$]").
    iApply (wpc_mono with "Hwp"); eauto.
    iIntros (?) "H Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "($&_)"; eauto. }
  iApply (wpc_mono with "H"); eauto.
  iIntros (?) "H". iApply "H".
  iApply wpc_crash_modality_intro; eauto.
Qed.

Lemma init_cancel_sep P1 Pc1 P2 Pc2 :
  init_cancel P1 Pc1 -∗
  init_cancel P2 Pc2 -∗
  init_cancel (P1 ∗ P2) (Pc1 ∗ Pc2).
Proof.
  iIntros "Hc1 Hc2".
  rewrite /init_cancel.
  iIntros (e s k Φ Φc Φc' mj Hlt) "Hwp".
  iApply ("Hc1" with "[//]"). iIntros "HP1".
  iApply ("Hc2" with "[//]"). iIntros "HP2".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_mono with "Hwp").
  { iIntros (?) "H Hwpc". iApply "H".
    iApply (wpc_crash_modality_wand with "Hwpc").
    iIntros "($&$&$)". eauto. }
  iIntros "H HPc2 HPc1". iApply "H". by iFrame.
Qed.

Lemma fupd_init_cancel P Pc :
  (|={⊤}=> init_cancel P Pc) -∗ init_cancel P Pc.
Proof.
  iIntros "H".
  iIntros (e s k Φ Φc ???) "Hwp".
  iApply (fupd_wpc).
  iMod "H". iModIntro.
  iApply "H"; eauto.
Qed.

Lemma init_cancel_fupd E P Pc :
  init_cancel (|={E}=> P) (|={E}=> Pc) -∗ init_cancel P Pc.
Proof.
  iIntros "H".
  iIntros (e s k Φ Φc ???) "Hwp".
  iApply wpc_cfupd.
  iApply "H"; auto. iIntros "HP".
  iApply (fupd_wpc).
  iMod (fupd_mask_subseteq E) as "Hclo"; first set_solver+.
  iMod "HP". iMod "Hclo". iModIntro.
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_mono with "Hwp").
  { iIntros (?) "H Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "(H&$)".
    iMod (fupd_mask_subseteq E) as "Hclo"; first set_solver+.
    iMod "H". iMod "Hclo". iModIntro. eauto. }
  iIntros "Hc HPC". iIntros "HC".
  iMod (fupd_mask_subseteq E) as "Hclo"; first set_solver+.
  iMod "HPC". iMod "Hclo". iModIntro.
  iApply "Hc". eauto.
Qed.

Lemma init_cancel_intro_l P :
  P -∗ init_cancel P True%I.
Proof.
  iIntros "HP".
  iIntros (e s k Φ Φc ???) "Hwp".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_mono with "Hwp").
  { iIntros (?) "H Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). eauto. }
  iIntros "H". iApply "H". eauto.
Qed.

Lemma init_cancel_intro_r P :
  P -∗ init_cancel True%I P.
Proof.
  iIntros "HP".
  iIntros (e s k Φ Φc ???) "Hwp".
  iSpecialize ("Hwp" with "[]"); first done.
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit; eauto.
  { iIntros (?) "H". iModIntro. iIntros "Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "$"; iFrame. eauto. }
  iIntros "H !>". iApply "H". eauto.
Qed.

Lemma init_cancel_intro P Pc :
  P -∗ Pc -∗ init_cancel P Pc.
Proof.
  iIntros "HP HPc".
  iIntros (e s k Φ Φc ???) "Hwp".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit; eauto.
  { iIntros (?) "H !> Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "$". eauto. }
  iIntros "H !>". iApply "H". eauto.
Qed.

Lemma init_cancel_shift P1 P2 Pc:
  init_cancel (P1 ∗ P2) Pc -∗ init_cancel P1 (Pc ∗ P2).
Proof.
  iIntros "H".
  iIntros (e s k Φ Φc ???) "Hwp".
  iApply "H"; auto. iIntros "(HP1&HP2)".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit; eauto.
  { iIntros (?) "H !> Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "($&$)". eauto. }
  iIntros "H !> HPC". iApply "H". by iFrame.
Qed.

Lemma init_cancel_wand P P' Pc Pc' :
  init_cancel P Pc -∗
  (P -∗ P') -∗
  (Pc -∗ Pc') -∗
  init_cancel P' Pc'.
Proof.
  iIntros "H H1 H2".
  iIntros (e s k Φ Φc ???) "Hwp".
  iApply "H"; auto. iIntros "HP".
  iDestruct ("H1" with "[$]") as "HP".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "[$]"); eauto.
  iSplit; first eauto.
  { iIntros (?) "H !> Hcm". iApply "H".
    iApply (wpc_crash_modality_wand with "Hcm"). iIntros "(H&$)".
    iApply "H2". eauto. }
  iIntros "H1 !> HPC". iApply "H1". iApply "H2". eauto.
Qed.

Lemma big_sepL_init_cancel {A} (Φ Φc : nat → A → iProp Σ) (l : list A) :
  ([∗ list] k ↦ x ∈ l, init_cancel (Φ k x) (Φc k x)) -∗
  init_cancel ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Φc k x).
Proof.
  iInduction l as [| x s] "IH" using rev_ind.
  - iIntros "_". iApply (init_cancel_intro); eauto.
  - iIntros "H". iDestruct (big_sepL_app with "H") as "(H1&H2)"; first eauto.
    iDestruct ("IH" with "[$]") as "H1".
    rewrite big_sepL_singleton.
    iDestruct (init_cancel_sep with "[$] [$]") as "H".
    iApply (init_cancel_wand with "H").
    * iIntros "(Hs&H)". iApply big_sepL_app; auto. iFrame; eauto.
    * iIntros "(Hs&H)". iApply big_sepL_app; auto. iFrame; eauto.
Qed.

Lemma big_sepS_init_cancel `{Countable A} (Φ Φc : A → iProp Σ) (s : gset A) :
  ([∗ set] x ∈ s, init_cancel (Φ x) (Φc x)) -∗
  init_cancel ([∗ set] x ∈ s, Φ x) ([∗ set] x ∈ s, Φc x).
Proof.
  iInduction s as [| x s] "IH" using set_ind_L.
  - iIntros "_". iApply (init_cancel_intro); eauto.
  - iIntros "H". iDestruct (big_sepS_insert with "H") as "(H1&H)"; first eauto.
    iDestruct ("IH" with "[$]") as "H".
    iDestruct (init_cancel_sep with "[$] [$]") as "H".
    iApply (init_cancel_wand with "H").
    * iIntros "(Hs&H)". iApply big_sepS_insert; auto. iFrame.
    * iIntros "(Hs&H)". iApply big_sepS_insert; auto. iFrame.
Qed.

End modality.
