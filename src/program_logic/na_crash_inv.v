From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl numbers.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre staged_wpc.
From Perennial.program_logic Require Export staged_wpc.
Set Default Proof Using "Type".
Import uPred.

Section ci.
Context `{!irisG Λ Σ}.
Context `{STAGED: !stagedG Σ}.
Context `{inG Σ (exclR unitO)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition na_crash_inv_def k Q P :=
  (∃ γ Q0 Qr, staged_value k O O ⊤ γ Q0 Qr P ∗ (Q0 -∗ Q) ∗ ▷ □ (Q -∗ P))%I.
Definition na_crash_inv_aux : seal (@na_crash_inv_def). by eexists. Qed.
Definition na_crash_inv := (na_crash_inv_aux).(unseal).
Definition na_crash_inv_eq := (na_crash_inv_aux).(seal_eq).

Ltac crash_unseal :=
  rewrite /na_crash_inv;
  rewrite ?na_crash_inv_eq;
  rewrite /na_crash_inv_def.

Lemma na_crash_inv_alloc k E P Q:
  ▷ Q -∗ ▷ □ (Q -∗ P) -∗ |(S k)={E}=> na_crash_inv (S k) Q P ∗ <disc> |C={⊤}_(S k)=> ▷ P.
Proof.
  crash_unseal.
  iIntros "HQ #HQP".
  iMod (staged_inv_alloc (k) E ⊤
                         P Q True%I with "[HQ]") as (i') "(#Hinv&Hval&Hpend)".
  { iFrame "#". iFrame. iModIntro; iIntros; eauto. iSplitL; last done.
    iApply "HQP"; eauto. }
  iModIntro.
  iSplitL "Hval".
  { iExists _, Q, _. iFrame. iFrame "#". auto. }
  iApply (staged_inv_init_cfupd' with "[Hpend]"); eauto.
Qed.

Lemma na_crash_inv_status_wand k Q P:
  na_crash_inv k Q P -∗
  ▷ □ (Q -∗ P).
Proof. crash_unseal. iDestruct 1 as (???) "(?&?&$)". Qed.

Lemma na_crash_inv_weaken k Q Q' P :
  (Q -∗ Q') -∗
  ▷ □(Q' -∗ P) -∗
  na_crash_inv k Q P -∗
  na_crash_inv k Q' P.
Proof.
  crash_unseal.
  iIntros "HQ' #HQ'P H".
  iDestruct "H" as (? Q0 Qr) "(Hval&Hwand0&#Hwand1)".
  iExists _, _, Qr. iFrame.
  iFrame "#". iIntros. iApply "HQ'". by iApply "Hwand0".
Qed.

Lemma wpc_na_crash_inv_open_modify Qnew s k k' k'' E1 e Φ Φc Q P :
  k'' ≤ k' →
  k'' ≤ (S k) →
  S k ≤ k' →
  na_crash_inv (S k') Q P -∗
  (<disc> ▷ Φc ∧ (▷ Q -∗ WPC e @ k''; E1
                    {{λ v, ▷ Qnew v ∗
                           ▷ □ (Qnew v -∗ P)  ∗ (na_crash_inv (S k') (Qnew v) P -∗ (<disc> ▷ Φc ∧ Φ v))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}.
Proof.
  crash_unseal.
  iIntros (???) "Hbundle Hwp".
  iDestruct "Hbundle" as (???) "(Hval&HQ0&HQP)".
  iApply (wpc_staged_inv_open' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Qnew _ with "[-]"); try iFrame "Hval"; eauto.
  { lia. }
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)". iIntros "HQ".
  iSpecialize ("Hwp" with "[HQ0 HQ]").
  { iNext. iApply "HQ0". eauto. }
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit.
  - iIntros (?) "(HQ&#Hwand'&HQrest)".
    iModIntro. iFrame "HQ Hwand'". iIntros "Hval'".
    iApply "HQrest". iFrame. iExists _, _, _. iFrame "∗ #". eauto.
  - by iIntros "!> H !>".
Qed.

(* TODO: in theory this can implement ElimAcc for iInv support; see
[elim_acc_wp_nonatomic] *)
Lemma wpc_na_crash_inv_open s k k' k'' E1 e Φ Φc Q P:
  k'' ≤ k' →
  k'' ≤ (S k) →
  S k ≤ k' →
  na_crash_inv (S k') Q P -∗
  (<disc> ▷ Φc ∧ (▷ Q -∗ WPC e @ k''; E1
                    {{λ v, ▷ Q ∗ (na_crash_inv (S k') Q P -∗ (<disc> ▷ Φc ∧ Φ v))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "H1 Hwp".
  iDestruct (na_crash_inv_status_wand with "H1") as "#Hwand".
  iApply (wpc_na_crash_inv_open_modify _ s k k' k'' with "[$] [Hwp]"); eauto.
  iSplit.
  - iDestruct "Hwp" as "($&_)".
  - iIntros "HQ". iDestruct "Hwp" as "(_&Hwp)". iSpecialize ("Hwp" with "[$]").
    iApply (wpc_mono' with "[] [] Hwp").
    * iIntros (?) "($&$)". eauto.
    * iModIntro. eauto.
Qed.

(* TODO, follows the pattern of staged_inv, the swap has to be atomic now *)
(*
Lemma na_crash_inv_open_modify N k' k E E' P Q R:
  ↑N ⊆ E →
  k' ≤ k →
  na_crash_inv (S k') Q P -∗
  ((▷ Q ∗ (∀ Q', ▷ Q' ∗ □ ▷ (Q' -∗ P) -∗ |(S k)={E∖↑N,E}=> na_crash_inv N (S k') Q' P)) ∨
   (C ∗ |(S k)={E∖↑N, E}=> na_crash_inv N (S k') Q P) -∗ |(S k)={E ∖ ↑N, E'}=> R) -∗
  (|(S k)={E,E'}=> R).
Proof.
  crash_unseal.
  iIntros (??) "Hbundle Hwp".
  iDestruct "Hbundle" as (???) "(Hval&HQ0Q&#HQP)".
  iPoseProof (staged_inv_open_modify E with "[$Hval]") as "HQ"; try solve_ndisj.
  iMod (fupd_level_le _ _ (S k') with "HQ") as "HQ"; first lia.
  iPoseProof (fupd_level_intro_mask' (E ∖ ↑N.@"1") (E ∖ ↑N)) as "Hclo0"; first solve_ndisj.
  iMod (fupd_level_le _ _ (S k') with "Hclo0") as "Hclo"; first lia.
  iApply ("Hwp" with "[HQ HQ0Q Hclo]").
  {
    iDestruct "HQ" as "[HQ1|HQ2]".
    * iLeft. iDestruct "HQ1" as "(HQ0&H)".
      iSplitL "HQ0Q HQ0".
      { iApply "HQ0Q". iNext. auto. }
      iIntros (?) "(HQ&#Hw)".
      iSpecialize ("H" $! _ True%I with "[-Hclo]").
      { iFrame "HQ". iIntros "!> H". iModIntro. iSplitR ""; last auto.
        iNext. by iApply "Hw". }
      iApply (fupd_level_le _ _ (S k')); first lia.
      iMod "Hclo".
      iMod ("H"). iModIntro. iExists _, _, _. iFrame "H Hw". eauto.
    * iRight. iDestruct "HQ2" as "(?&$&H)".
      iMod (fupd_level_le with "Hclo"); first lia.
      iMod (fupd_level_le with "H"); first lia.
      iModIntro. iExists _, _, _. iFrame. eauto.
  }
Qed.

Lemma na_crash_inv_open N k' k E E' P Q R:
  ↑N ⊆ E →
  k' ≤ k →
  na_crash_inv N (S k') Q P -∗
  ((▷ Q ∗ (▷ Q ∗ □ ▷ (Q -∗ P) -∗ |(S k)={E∖↑N,E}=> na_crash_inv N (S k') Q P)) ∨
   (C ∗ |(S k)={E∖↑N, E}=> na_crash_inv N (S k') Q P) -∗ |(S k)={E ∖ ↑N, E'}=> R) -∗
  (|(S k)={E,E'}=> R).
Proof.
  iIntros (??) "H1 H2".
  iApply (na_crash_inv_open_modify with "[$]"); auto.
  iIntros "H". iApply ("H2" with "[H]").
  iDestruct "H" as "[H1|H2]".
   - iLeft. iDestruct "H1" as "($&H)". iIntros "HQ". by iMod ("H" $! Q with "[$]").
   - iRight. iFrame.
Qed.
*)

End ci.
