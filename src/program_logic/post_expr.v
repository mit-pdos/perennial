From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt.
Set Default Proof Using "Type".
Import uPred.

Section modality.
Context `{IRISG: !irisGS Λ Σ}.

Definition post_expr (E : coPset) (P : iProp Σ) : iProp Σ :=
  (∀ e k E' Φ (Hsub: E ⊆ E') (Hnval : to_val e = None),
    (WPC e @ NotStuck; k; E' {{ λ v, P -∗ Φ v }} {{  True }}) -∗
    WPC e @ NotStuck; k; E' {{ λ v, Φ v }} {{ True }}).

Lemma post_expr_elim k e E E' Φ P :
  E ⊆ E' →
  to_val e = None →
  post_expr E P -∗
  (WPC e @ NotStuck; k; E' {{ λ v, P -∗ Φ v }} {{ True }}) -∗
  WPC e @ NotStuck; k; E' {{ Φ }} {{ True }}.
Proof.
  iIntros (??) "H1 H2". rewrite /post_expr. iSpecialize ("H1" with "[//] [//] [$]").
  iApply (wpc_mono with "H1"); auto.
Qed.

Lemma post_expr_intro E P :
  P -∗ post_expr E P.
Proof.
  iIntros "HP". iIntros (??????) "H".
  iApply (wpc_strong_mono with "H [HP]"); auto.
  iSplit; last eauto.
  iIntros (?) "H !>". by iApply "H".
Qed.

Lemma post_expr_sep E P1 P2 :
  post_expr E P1 -∗
  post_expr E P2 -∗
  post_expr E (P1 ∗ P2).
Proof.
  iIntros "Hc1 Hc2".
  iIntros (??????) "Hwp".
  iApply (post_expr_elim with "Hc2"); auto.
  iApply (post_expr_elim with "Hc1"); auto.
  iApply (wpc_mono with "Hwp"); auto.
  iIntros (?) "H H1 H2". iApply "H". by iFrame.
Qed.

Lemma fupd_post_expr E E' P :
  E ⊆ E' →
  (|={E}=> post_expr E' P) -∗ post_expr E' P.
Proof.
  iIntros (?) "H".
  iIntros (??????) "Hwp".
  iMod (fupd_mask_mono with "H") as "H"; first set_solver.
  iApply (post_expr_elim with "H"); auto.
Qed.

Lemma post_expr_wand E P Q:
  (P ={E}=∗ Q) -∗
  post_expr E P -∗ post_expr E Q.
Proof.
  iIntros "HPQ H".
  iIntros (??????) "Hwp".
  iApply wpc_fupd.
  iApply (post_expr_elim with "H"); auto.
  iApply (wpc_strong_mono with "Hwp [HPQ]"); auto.
  iSplit; last eauto.
  iIntros (v) "H !> HP". iMod (fupd_mask_mono with "(HPQ HP)"); auto.
  iApply "H"; eauto.
Qed.

End modality.
