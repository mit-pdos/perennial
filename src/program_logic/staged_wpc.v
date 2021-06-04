From iris.proofmode Require Import base tactics classes.
From Perennial.Helpers Require Import ipm.
From iris.algebra Require Import excl numbers.
From iris.bi Require Export laterable.
From Perennial.base_logic Require Export invariants.
From Perennial.program_logic Require Export weakestpre.
From Perennial.algebra Require Export abs_laterable.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre.
Set Default Proof Using "Type".
Import uPred.

Section staged_inv_wpc.
Context `{!irisGS Λ Σ}.
Context `{!stagedG Σ}.
Context `{inG Σ (exclR unitO)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma staged_inv_init_bdisc_cfupd γ k k' E1 P:
  k' ≤ k →
  staged_inv (S k') E1 γ P ∗
  staged_pending 1%Qp γ -∗
  (<bdisc> |C={E1}_(S k)=> ▷P).
Proof.
  iIntros (Hle)  "(#Hinv&Hpending)".
  iModIntro. iIntros "HC".
  iPoseProof (staged_inv_weak_open E1 k' (E1) with "[Hinv $Hpending $HC]") as "H"; auto.
  iMod (fupd_level_le with "H") as "HP"; first by lia.
  do 2 iModIntro. auto.
Qed.

Lemma staged_inv_init_cfupd' γ k k' E1 P:
  k' ≤ k →
  staged_inv (S k') E1 γ P ∗
  staged_pending 1%Qp γ -∗
  (<disc> |C={E1}_(S k)=> ▷P).
Proof.
  iIntros (Hle)  "(#Hinv&Hpending)".
  iModIntro. iIntros "HC".
  iPoseProof (staged_inv_weak_open E1 k' (E1) with "[Hinv $Hpending $HC]") as "H"; auto.
  iMod (fupd_level_le with "H") as "HP"; first by lia.
  do 2 iModIntro. auto.
Qed.

Lemma wpc_staged_inv_init' γ s k k' E1 e Φ Φc P:
  k' ≤ k →
  staged_inv (S k') E1 γ P ∗
  staged_pending 1%Qp γ ∗
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc ∗ ▷ P }}.
Proof.
  iIntros (Hle) "(#Hinv&Hpending&H)".
  iApply (wpc_strong_crash_frame s s _ _ E1 _ _ with "H"); try auto.
  iApply (staged_inv_init_cfupd'); eauto.
Qed.

(* Like staged value, except that it can be opened without getting a later, because
   it says that ▷ of what's stored implies Q *)
Definition staged_value_later k1 k2 mj E E' γ Q Q' P : iProp Σ :=
  (∃ Q0 Q1, (▷ Q0-∗ ◇ Q) ∗
            <disc> (▷ Q1 -∗ ◇ Q') ∗
      □ (▷ Q0 -∗ ▷ C -∗ |k2, Some (S mj)={E'}=> ▷ P ∗ ▷ Q1) ∗
      staged_value k1 k2 mj E γ Q0 Q1 P)%I.

(* XXX what about stripping the later off Qr? maybe we put one later in the definition of wpc after the viewshifts in the crash condition? *)
(*
Lemma staged_inv_later_open E k k2 N1 N2 E1 γ P Q Qr:
  N1 ## N2 →
  ↑N1 ⊆ E →
  ↑N2 ⊆ E →
  staged_value_later (S k) k2 N1 N2 E1 γ Q Qr P -∗ |(S k)={E,E∖↑N1}=>
  (Q ∗ (∀ Q' Qr' Q0, ▷ Q0 ∗ (▷ Q0-∗ ◇ Q') ∗
   □ (▷ Q0 -∗ |C={E1, ∅}_k=> ▷ P ∗ ▷ Qr') -∗ |(S k)={E∖↑N1,E}=> staged_value_later (S k) k2 N1 N2 E1 γ Q' Qr' P)) ∨
  (▷ Qr ∗ C ∗ |(S k)={E∖↑N1, E}=> staged_value_later (S k) k2 N1 N2 E1 γ Q True P).
Proof.
  iIntros (???) "Hinv".
  iDestruct "Hinv" as (Q0) "(Hwand&Hinv)".
  iMod (staged_inv_open_modify with "Hinv") as "[HQ0|Hcrash]"; auto.
  - iDestruct "HQ0" as "(HQ0&Hclo)".
    iMod ("Hwand" with "HQ0") as "HQ".
    iModIntro. iLeft. iFrame "HQ".
    iIntros (Q' Qr' Q0'). iIntros "(HQ0'&Hwand'&#Hwand'')".
    iMod ("Hclo" $! Q0' Qr' with "[$HQ0' $Hwand'']").
    iModIntro. iExists Q0'; iFrame.
  - iRight. iModIntro. iDestruct "Hcrash" as "($&$&Hfinish)".
    iMod "Hfinish". iModIntro. iExists Q0. by iFrame "# ∗".
Qed.
*)

(* WPC without the other most fupd *)
Definition wpc_no_fupd s k mj E1 e1 Φ Φc :=
  ((match to_val e1 with
   | Some v => ∀ q, NC q -∗ |={E1}=> Φ v ∗ NC q
   | None => ∀ q σ1 g1 ns κ κs nt,
      state_interp σ1 nt -∗ global_state_interp g1 ns (κ ++ κs) -∗ NC q -∗ |={E1,∅}=> |={∅}▷=>^(S $ num_laters_per_step ns)
        (⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
        ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |={∅,E1}=>
          (state_interp σ2 (length efs + nt) ∗
          global_state_interp g2 (S ns) κs ∗
          wpc0 s k mj E1 e2 Φ Φc ∗
          ([∗ list] i ↦ ef ∈ efs, wpc0 s k mj ⊤ ef fork_post True) ∗
          NC q))
   end ∧
   (<disc> (C -∗ |k,(Some mj)={E1}=> Φc))))%I.

Lemma staged_inv_later_open' E k k2 mj2 E1 E2 γ P Q Qr Q' Qr' R:
  k2 ≤ k →
  staged_value_later (S k) k2 mj2 E1 E2 γ Q Qr P -∗
  (Q -∗ |k, Some O={E}=> □ (▷ Q' -∗ C -∗ |k2,Some (S mj2)={E1}=> ▷ P ∗ ▷ Qr') ∗  ▷ Q' ∗ R) -∗
  |(S k)={E}=> (R ∗ staged_value (S k) k2 mj2 E1 γ Q' Qr' P) ∨
               (Qr ∗ C).
Proof.
  iIntros (?) "Hinv Hshift".
  iDestruct "Hinv" as (Q0 Q1) "(Hwand1&Hwand1'&#Hwand2&Hinv)".
  iMod (staged_inv_open_modify_ae _ k k2 k2 mj2 mj2 with "Hinv [Hwand1 Hshift]") as "[HQ0|Hcrash]"; auto.
  {
    iIntros "HQ0".
    iMod ("Hwand1" with "HQ0") as "HQ".
    iMod ("Hshift" with "HQ") as "HQ".
    iModIntro. iFrame.
  }
  { iModIntro. iFrame. }
  { iDestruct "Hcrash" as "(HQ1&HC)".
    iMod (own_disc_fupd_level_elim with "Hwand1'") as "Hwand1'".
    iMod ("Hwand1'" with "HQ1") as "HQ".
    iModIntro. iRight. iFrame. }
Qed.

Lemma wpc_staged_inv_open_aux' γ s k k' k'' k0post j jpost E1 E1' e Φ Φc {HL: AbsLaterable Φc} P q:
  E1 ⊆ E1' →
  (* The level we move to (k'') must be < (S k'), the level of the staged invariant.
     However, it may be the same as (S k), the wpc we were originally proving. Thus,
     no "fuel" is lost except what is needed to be "below" the invariant's universe level *)
  k'' ≤ k' →
  k'' ≤ (S k) →
  (S k ≤ k') →
  (k0post ≤ k') →
  NC q ∗
  staged_value_later (S k') k'' j E1' E1 γ
               (wpc_no_fupd NotStuck k'' (S j) E1 e
                   (λ v, ∃ Q, ▷ Q ∗ □ (▷ Q -∗ |C={E1'}_k0post=> ▷ P) ∗ (staged_value (S k') k0post jpost E1' γ
                                                                Q True (P) -∗ |={E1}=> <disc> (|C={E1}_k=> Φc) ∧ Φ v))%I
                   (Φc ∗ ▷ P))
                Φc
                (P)%I
  ⊢ |={E1}=> wpc0 s (S k) j E1 e Φ Φc ∗ NC q.
Proof.
  iIntros (?? Hle1 Hle2 Hle3) "(HNC&Hwp)".
  iLöb as "IH" forall (e q).
  destruct (to_val e) as [v|] eqn:Hval.
  {
    iDestruct (NC_split with "HNC") as "(HNC1&HNC2)".
    iPoseProof (staged_inv_later_open' E1 _ _ _ _ _ _ _ _ _ (NC (q/2)) True%I
                                       (wpc_no_fupd NotStuck k'' _ E1 e
                                                    (λ v0, ∃ Q, ▷ Q ∗  □ (▷ Q -∗ |C={E1'}_k0post=> ▷ P)
                                                             ∗ (staged_value (S k') _ _ E1' γ Q True P
                                                                             -∗ |={E1}=> <disc> (|C={E1}_k=> Φc)
                                                                                         ∧ Φ v0))%I
                                                    (Φc ∗ ▷ P)%I)
                  with "Hwp [HNC1]") as "H"; first lia.
    { iIntros "$". iModIntro. iFrame. iModIntro. iIntros ">HNC HC". iDestruct (NC_C with "[$] [$]") as %[]. }
    iMod (fupd_level_fupd with "H") as "[(H&Hval)|Hcrash]"; last first.
    { iDestruct "Hcrash" as "(_&HC)". iDestruct (NC_C with "[$] [$]") as "[]". }
    {
      rewrite /wpc_no_fupd.
      rewrite wpc0_unfold /wpc_pre.
      rewrite Hval.
      iDestruct "H" as "(H&_)".
      iMod ("H" with "[$]") as "((%Q&HQ&#HQP&HΦ)&HNC)".
      iPoseProof (staged_inv_open_modify_ae E1 _ _ k0post j jpost _ _ _ _ _ Q True%I (NC (q/2))
                  with "Hval [HQ]") as "H"; try lia.
      { iIntros ">$". iModIntro. iFrame. iModIntro.
        iIntros "HQ HC".
        iSpecialize ("HQP" with "[$] [$]").
        iMod (fupd_level_split_level with "HQP"); first lia.
        iModIntro. iSplitR ""; last done. iNext. eauto. }
      iMod (fupd_level_fupd with "H") as "[(H&Hval)|Hcrash]"; last first.
      { iDestruct "Hcrash" as "(_&HC)". iDestruct (NC_C with "[$] [$]") as "[]". }
      iModIntro. iDestruct (NC_join with "[$]") as "$".
      iMod ("HΦ" with "Hval") as "H".
      iModIntro.
      iSplit.
      - iIntros (?) "HNC". iDestruct "H" as "(_&?)". iModIntro. iFrame.
      - iLeft in "H". iModIntro. iIntros "HC". iSpecialize ("H" with "[$]").
        iMod (fupd_level_split_level with "H"); first lia.
        iModIntro; eauto.
    }
  }
  iModIntro.
  iEval (rewrite wpc0_unfold /wpc_pre). rewrite Hval.
  iSplitR "HNC"; last by auto.
  iModIntro.
  iSplit; last first.
  {
    rewrite /staged_value_later.
    iDestruct "Hwp" as (Q0 Q1) "(?&HΦcwand&#Hwand0&Hwp)".
    iDestruct (staged_value_into_disc with "Hwp") as "Hwp".
    iModIntro. iIntros "HC".
    iPoseProof (staged_inv_disc_open_crash with "[] Hwp HC") as "H"; try assumption.
    {
      iModIntro. iIntros "HQC >HC".
      iDestruct ("Hwand0" with "[$] [$]") as "Hwp".
      iMod "Hwp". by iModIntro.
    }
    iMod (fupd_split_level_le with "H"); first (naive_solver lia).
    by iDestruct ("HΦcwand" with "[$]") as ">$".
  }
  iIntros (???????) "Hσ Hg HNC".
  iDestruct (NC_split with "HNC") as "(HNC1&HNC2)".
  iPoseProof (staged_inv_later_open' E1 _ _ _ _ _ _ _ _ _ (NC (q0/2)) True%I
                                       (wpc_no_fupd NotStuck k'' _ E1 e
                                                    (λ v0, ∃ Q, ▷ Q ∗ □ (▷ Q -∗ |C={E1'}__=> ▷ P)
                                                             ∗ (staged_value (S k') _ _ E1' γ Q True P
                                                                             -∗ |={E1}=> <disc> (|C={E1}_k=> Φc) ∧ Φ v0))%I
                                                    (Φc ∗ ▷ P))
                with "Hwp [HNC1]") as "H"; first lia.
  iIntros.
  { iFrame.  iModIntro. iModIntro. iIntros ">HNC HC". iDestruct (NC_C with "[$] [$]") as %[]. }
  iMod (fupd_level_fupd with "H") as "[(Hwp&Hclo')|Hcrash]"; last first.
  {
    iDestruct "Hcrash" as "(HΦc&HC)".
    iDestruct (NC_C with "[$] [$]") as "[]".
  }
  iDestruct "Hwp" as "(H&_)".
  rewrite Hval.
  iMod ("H" with "[$] [$] [$]") as "H".
  iModIntro.
  simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "(%&H)".
  iSplitL "".
  { by destruct s; auto. }
  iIntros. iMod ("H" with "[//]") as "H".
  iDestruct "H" as "(Hσ&Hg&H&Hefs&HNC)".
  iEval (rewrite wpc0_unfold /wpc_pre) in "H". iMod "H".
  rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
  iDestruct (own_discrete_elim_conj with "H") as (Q_keep Q_inv) "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
  iDestruct (abs_laterable Φc) as (Q1) "#HQ1".
  iPoseProof (staged_inv_open_modify_ae E1 _ _ k'' j j E1' γ _ _ _
                                        Q_inv Q1 (NC (q0/2))
                with "Hclo' [HQ_inv]") as "H"; try lia.
  {
    iIntros ">HNC".
    iFrame. do 2 iModIntro.
    iIntros "HQ HC".
    iDestruct ("Hwand1" with "[$]") as ">H".
    iEval (rewrite uPred_fupd_level_eq) in "H".
    iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo_empty"; first by set_solver.
    iMod (fupd_split_level_le with "H") as "H"; first by (naive_solver lia).
    iMod "Hclo_empty" as "_".
    iMod (fupd_split_level_intro_mask' _ E1) as "Hclo"; first by set_solver.
    iMod ("H" with "[$]") as "(HΦc&$)".
    iDestruct ("HQ1" with "[$]") as "$".
    iMod "Hclo".
    iModIntro. eauto.
  }
  iMod (fupd_level_fupd with "H") as "[(HNC2&Hval)|(_&Hfalse)]"; last first.
  { iDestruct (NC_C with "[$] [$]") as %[]. }
  iDestruct (NC_join with "[$]") as "HNC".
  iFrame "Hσ".
  iMod ("IH" with "HNC [Hval HQ_keep]") as "(Hwp&HNC)".
  { iExists Q_inv, Q1.
    iFrame "Hval".  iSplitL "HQ_keep"; [| iSplitL ""].
    - iIntros "HQ". rewrite /wpc_no_fupd own_discrete_fupd_eq.
      iSpecialize ("Hwand2" with "[$]"). iApply "Hwand2".
    - iModIntro; eauto. iIntros "?". by iApply "HQ1".
    - iModIntro. iIntros "HQ >HC". iMod ("Hwand1" with "[$]") as "H".
      iSpecialize ("H" with "[$]").
      iDestruct "HQ1" as "-#HQ1".
      iClear "#". rewrite uPred_fupd_level_eq.
      iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo_empty"; first by set_solver.
      iMod (fupd_split_level_le with "H") as "H"; first by (naive_solver lia).
      iMod "Hclo_empty" as "_".
      iMod "H" as "(HΦc&$)".
      iModIntro. by iApply "HQ1".
  }
  iModIntro.
  iFrame.
  iApply (big_sepL_mono with "Hefs").
  iIntros. iApply (wpc0_strong_mono with "[$]"); eauto.
  { naive_solver lia. }
Qed.

(** This key rule is the reason why there is a <disc> in the definition of WPC:
We need to put the WPC with crash condition [Φc ∗ ▷ P] into a (staged)
invariant, and still be able to get it out without a ▷ in the non-crash
case. This relies on [own_discrete_elim_conj] to put "only the discrete part" of
the WPC into the invariant, and keep the other resources backing this WPC
locally to ourselves. *)
Lemma wpc_staged_inv_open' γ s k k' k'' k2 mj E1 E1' e Φ Φc {HL: AbsLaterable Φc} Q Qrest P :
  E1 ⊆ E1' →
  k'' ≤ k' →
  k'' ≤ (S k) →
  (S k) ≤ k' →
  k2 ≤ k' →
  k'' ≤ k2 →
  staged_value (S k') k2 mj E1' γ Q Qrest P ∗
  (<disc> Φc ∧
  (▷ Q -∗
   WPC e @ NotStuck; k''; E1
      {{λ v, ∃ Qnew, ▷ Qnew ∗
             □ (▷ Qnew -∗ |C={E1'}_k2=> ▷ P) ∗
            (staged_value (S k') k2 mj E1' γ Qnew True P -∗ |={E1}=> (<disc> (|C={E1}_k=> Φc) ∧ Φ v))}}
      {{ Φc ∗ ▷ P }}))
  ⊢
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??????) "(Hval&Hwp)".
  rewrite wpc_unfold.
  iIntros (j').
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite /wpc_pre.
    rewrite Hval. iModIntro.
    iSplit.
    - iIntros (?) "HNC".
      iDestruct (NC_split with "HNC") as "(Hnc1&Hnc2)".
      (* Swap in NC *)
      iPoseProof (staged_inv_open_modify_ae E1 _ _ _ _ _ _ _ _ _ _ (NC (q/2)) True%I (▷Q)%I
                  with "Hval [Hnc2]") as "H"; try auto.
      {
        iIntros "$". iFrame. iModIntro. iIntros "!> >HNC HC".
        iDestruct (NC_C with "[$] [$]") as %[].
      }

      iMod (fupd_level_fupd with "H") as "[(H&Hclo')|Hcrash]"; last first.
      {
        iDestruct "Hcrash" as "(HΦc&HC)".
        iDestruct (NC_C with "[$] [$]") as "[]".
      }
      iDestruct "Hwp" as "(_&Hwp)".
      rewrite wpc_unfold /wpc_pre.
      rewrite Hval.
      iSpecialize ("Hwp" with "[$]").
      iMod ("Hwp" $! (S j')) as "(H&_)".
      iMod ("H" $! _ with "[$]") as "((%Qnew&HQ&#HQP&Hwand)&Hnc)".
      iPoseProof (staged_inv_open_modify_ae E1 _ _ k2 mj mj _ _ _ _ _ (Qnew) True%I (NC (q/2))%I
                  with "Hclo' [HQ]") as "H"; try auto.
      {
        iIntros ">$". iFrame. iModIntro. iIntros "!> HQ HC".
        iSpecialize ("HQP" with "[$] [$]").
        iMod (fupd_level_split_level with "HQP"); first lia. iFrame.
        iModIntro. eauto.
      }
      iMod (fupd_level_fupd with "H") as "[(H&Hclo')|Hcrash]"; last first.
      {
        iDestruct "Hcrash" as "(HΦc&HC)".
        iDestruct (NC_C with "[$] [$]") as "[]".
      }
      iMod ("Hwand" with "[$]") as "(_&$)".
      iModIntro.
      iApply (NC_join with "[$]").
    - iDestruct "Hwp" as "(Hwp&_)". iModIntro. iIntros. by iModIntro.
    }
  iEval (rewrite /wpc_pre).
  iModIntro.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(Hwp&_)". iModIntro. iIntros. by iModIntro.
  }
  rewrite Hval.
  iIntros (???????) "Hσ Hg HNC".
  iDestruct (NC_split with "HNC") as "(Hnc1&Hnc2)".

  iPoseProof (staged_inv_open_modify_ae E1 _ _ _ _ _ _ _ _ _ _ (NC (q/2)) True%I (▷Q)%I
              with "Hval [Hnc2]") as "H"; try auto.
  {
    iIntros "$". iFrame. iModIntro. iIntros "!> >HNC HC".
    iDestruct (NC_C with "[$] [$]") as %[].
  }
  iMod (fupd_level_fupd with "H") as "[(H&Hclo')|Hcrash]"; last first.
  {
    iDestruct "Hcrash" as "(HΦc&HC)".
    iDestruct (NC_C with "[$] [$]") as "[]".
  }
  iDestruct "Hwp" as "(_&Hwp)".
  rewrite wpc_unfold /wpc_pre.
  rewrite Hval.
  iSpecialize ("Hwp" with "[$]").
  iMod ("Hwp" $! (S j')) as "(H&_)".
  iMod ("H" with "[$] [$] [$]") as "H".
  simpl. iMod "H". iModIntro. iModIntro. iNext. iMod "H". iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "(%&H)".
  iSplitL "".
  { destruct s; eauto. }
  iIntros.
  iMod ("H" with "[//]") as "H".
  iDestruct "H" as "(Hσ&Hg&H&Hefs&HNC)".
  iEval (rewrite wpc0_unfold /wpc_pre) in "H". iMod "H".
  rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
  iDestruct (own_discrete_elim_conj with "H") as (Q_keep Q_inv) "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
  iDestruct (abs_laterable Φc) as (Q1) "#HQ1".
  iPoseProof (staged_inv_open_modify_ae E1 _ _ k'' j' j' E1' γ _ _ _
                                        Q_inv Q1 (NC (q/2))
                with "Hclo' [HQ_inv]") as "H"; try lia.
  {
    iIntros ">HNC".
    iFrame. do 2 iModIntro.
    iIntros "HQ HC".
    iDestruct ("Hwand1" with "[$]") as ">H".
    iEval (rewrite uPred_fupd_level_eq) in "H".
    iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo_empty"; first by set_solver.
    iMod (fupd_split_level_le with "H") as "H"; first by (naive_solver lia).
    iMod "Hclo_empty" as "_".
    iMod (fupd_split_level_intro_mask' _ E1) as "Hclo"; first by set_solver.
    iMod ("H" with "[$]") as "(HΦc&$)".
    iMod "Hclo". iModIntro. by iApply "HQ1".
  }
  iMod (fupd_level_fupd with "H") as "[(HNC2&Hval)|(_&Hfalse)]"; last first.
  { iDestruct (NC_C with "[$] [$]") as %[]. }
  iDestruct (NC_join with "[$]") as "HNC".
  iFrame "Hσ Hg".
  iPoseProof (wpc_staged_inv_open_aux' γ s k k' k'' k2 j' mj E1 E1'
                e2 Φ Φc P with "[Hval HQ_keep HNC]") as "H"; try assumption.

  { iFrame. iExists _, _. iFrame "Hval".  iSplitL "HQ_keep"; [ | iSplitL ""].
    - iIntros "HQ". iMod ("Hwand2" with "[$]") as "H".
      rewrite /wpc_no_fupd own_discrete_fupd_eq.
      iExact "H".
    - iModIntro. iIntros. by iApply "HQ1".
    - iModIntro. iIntros "HQ >HC". iMod ("Hwand1" with "[$]") as "H".
      iSpecialize ("H" with "[$]").
      rewrite uPred_fupd_level_eq.
      iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo_empty"; first by set_solver.
      iMod (fupd_split_level_le with "H") as "H"; first by (naive_solver lia).
      iMod "Hclo_empty" as "_".
      iMod "H" as "(HΦC&$)". iModIntro. by iApply "HQ1".
  }
  iMod "H" as "($&$)".
  iApply (big_sepL_mono with "Hefs").
  iIntros. iApply (wpc0_strong_mono with "[$]"); eauto.
  - naive_solver lia.
Qed.

Lemma big_sepS_impl_cfupd `{Countable A} (Φ Ψ: A -> iProp Σ) (s : gset A) E k :
  ([∗ set] a∈s, Φ a) -∗
  □ (∀ x, ⌜x ∈ s⌝ -∗ Φ x -∗ |C={E}_k=> Ψ x)
  -∗ |C={E}_k=>
  ([∗ set] a∈s, Ψ a).
Proof.
  iIntros "H #Hupd".
  iInduction s as [|x X ? s] "IH" using set_ind_L.
  { iModIntro. iApply big_sepS_empty. done. }
  repeat rewrite -> big_sepS_union by set_solver.
  iDestruct "H" as "[Hx H]".
  iMod ("IH" with "[Hupd] H") as "H".
  { iModIntro. iIntros (y Hy). iApply "Hupd". iPureIntro. set_solver. }
  rewrite !big_sepS_singleton.
  iMod ("Hupd" with "[] Hx") as "Hx".
  { iPureIntro. set_solver. }
  iModIntro.
  iFrame.
Qed.

Lemma big_sepM_impl_cfupd `{Countable A} {V} (Φ Ψ: A -> V -> iProp Σ) (m : gmap A V) E k :
  ([∗ map] a↦v∈m, Φ a v) -∗
  □ (∀ a x, ⌜m !! a = Some x⌝ -∗ Φ a x -∗ |C={E}_k=> Ψ a x)
  -∗ |C={E}_k=>
  ([∗ map] a↦v∈m, Ψ a v).
Proof.
  iIntros "H #Hupd".
  iInduction m as [|x m] "IH" using map_ind.
  { iModIntro. iApply big_sepM_empty. done. }
  repeat rewrite -> big_sepM_insert by eauto.
  iDestruct "H" as "[Hx H]".
  iMod ("IH" with "[Hupd] H") as "H".
  { iModIntro. iIntros (a y Hy). iApply "Hupd". iPureIntro.
    rewrite lookup_insert_ne; eauto. intro Hx; subst; congruence. }
  iMod ("Hupd" with "[] Hx") as "Hx".
  { iPureIntro. rewrite lookup_insert. done. }
  iModIntro.
  iFrame.
Qed.

(*
Lemma cfupd_big_sepS `{Countable A} (σ: gset A)(P: A → iProp Σ) k E1  :
  ([∗ set] a ∈ σ, |C={E1, ∅}_(LVL k)=> P a) -∗
  |C={E1, ∅}_(LVL (size σ + k))=> ([∗ set] a ∈ σ, P a).
Proof.
  iIntros "H".
  iInduction σ as [| x σ ?] "IH" using set_ind_L.
  - iModIntro. iNext.
    rewrite big_sepS_empty //.
  - rewrite -> !big_sepS_union by set_solver.
    rewrite !big_sepS_singleton.
    iDestruct "H" as "(Hx & Hrest)".
    rewrite size_union; last by set_solver.
    rewrite size_singleton.
    iMod "Hx".
    { simpl.
      rewrite LVL_Sk.
      pose proof (LVL_gt (size σ+k)).
      rewrite LVL_sum_split.
      abstract_pow4. }
    iFrame "Hx".
    iMod ("IH" with "Hrest") as "Hrest".
    { change (1 + size σ + k) with (S (size σ + k)).
      rewrite LVL_Sk.
      pose proof (LVL_gt (size σ + k)).
      pose proof (LVL_le k (size σ + k)).
      nia. }
    iModIntro. iModIntro.
    iFrame.
Qed.

Lemma cfupd_big_sepL_aux {A} (l: list A) (Φ: nat → A → iProp Σ) n k E1 :
  ([∗ list] i↦a ∈ l, |C={E1, ∅}_(LVL k)=> Φ (n + i) a) -∗
  |C={E1, ∅}_(LVL (length l + k))=> ([∗ list] i↦a ∈ l, Φ (n + i) a).
Proof.
  iIntros "H".
  (iInduction l as [| x l] "IH" forall (n)).
  - iModIntro. iNext.
    simpl; auto.
  - rewrite -> !big_sepL_cons by set_solver.
    simpl.
    iDestruct "H" as "(Hx & Hrest)".
    iMod "Hx".
    { simpl.
      rewrite LVL_Sk.
      pose proof (LVL_gt (length l+k)).
      rewrite LVL_sum_split.
      abstract_pow4. }
    iFrame "Hx".
    assert (forall k, n + S k = S n + k) as Harith by lia.
    setoid_rewrite Harith.
    iMod ("IH" with "Hrest") as "Hrest".
    { rewrite LVL_Sk.
      pose proof (LVL_gt (length l + k)).
      pose proof (LVL_le k (length l + k)).
      nia. }
    iModIntro. iModIntro.
    iFrame.
Qed.

Lemma cfupd_big_sepL {A} (l: list A) (Φ: nat → A → iProp Σ) k E1 :
  ([∗ list] i↦a ∈ l, |C={E1, ∅}_(LVL k)=> Φ i a) -∗
  |C={E1, ∅}_(LVL (length l + k))=> ([∗ list] i↦a ∈ l, Φ i a).
Proof. iApply (cfupd_big_sepL_aux _ _ 0). Qed.

Lemma wpc_crash_frame_big_sepS_wand `{Countable A} (σ: gset A)(P: A → iProp Σ) k s E2 e Φ Φc  :
  ([∗ set] a ∈ σ, ∃ k', ⌜ k' ≤ k ⌝ ∗ |C={⊤, ∅}_(LVL k')=> P a) -∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ ([∗ set] a ∈ σ, P a) -∗ Φc }} -∗
  WPC e @ s; LVL (S k + size σ); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hs Hwpc".
  iDestruct (cfupd_big_sepS with "[Hs]") as "Hs".
  { iApply (big_sepS_mono with "Hs").
    iIntros (x ?) "H".
    iDestruct "H" as (k') "[% H]".
    iApply (cfupd_weaken_all _ (LVL k) with "H"); auto.
    apply LVL_le; auto. }
  simpl.
  iMod "Hs" as "_".
  { lia. }
  iApply (wpc_idx_mono with "Hwpc").
  apply LVL_le; lia.
Qed.

Lemma wpc_staged_inv_init Γ s k k' N E1 E2 e Φ Φc P i :
  k' < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (LVL k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  rewrite /LVL. iIntros (??) "(?&?&?)".
  replace (base ^ (S (S (S k)))) with (base * (base ^ ((S (S k))))) by auto.
  iApply (wpc_idx_mono _ (2 * base ^ (S (S k)))).
  {  lia. }
  iApply wpc_staged_inv_init''; last first. iFrame; auto.
  - eauto.
  - transitivity (base)%nat; first by auto. replace base with (base^1) by auto. apply Nat.pow_lt_mono_r_iff; eauto => //=. lia.
    lia.
  - apply (lt_le_trans _ (base * (base ^ (S (S k'))))).
    cut (1 < base ^ (S (S k'))); try lia.
    { replace 1 with (base^0) by auto. apply Nat.pow_lt_mono_r_iff; lia. }
    rewrite -PeanoNat.Nat.pow_succ_r'. apply Nat.pow_le_mono_r_iff; lia.
Qed.

Lemma wpc_staged_inv_init_wand Γ s k k' N E1 E2 e Φ Φc P i :
  k' < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (LVL k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ P -∗ Φc }} ⊢
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "(Hstaged&Hcrash&Hwp)".
  iAssert (WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ (P -∗ Φc) ∗ P }})%I with "[-]" as "Hwp"; last first.
  { iApply (wpc_mono with "Hwp"); auto. rewrite wand_elim_l //. }
  by iApply (wpc_staged_inv_init with "[$]").
Qed.

Lemma wpc_staged_inv_open Γ s k k' E1 E1' E2 e Φ Φc Q Qrest Qnew P N b bset :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  staged_inv Γ N (LVL k') (E1' ∖ ↑N) (E1' ∖ ↑N) ∗
  staged_bundle Γ Q Qrest b bset ∗
  staged_crash Γ P bset ∗
  (Φc ∧ ((Q) -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅ {{λ v, ▷ Qnew v ∗ ▷ □ (Qnew v -∗ P) ∗ (staged_bundle Γ (Qnew v) True false bset -∗  (Φc ∧ Φ v))}} {{ Φc ∗ ▷ P }})) ⊢
  WPC e @ s; LVL ((S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite /LVL. iIntros (????) "(?&?&?)".
  assert (Hpow: base ^ (S (S (S k))) =  4 * base ^ (S (S k))).
  { rewrite //=. }
  rewrite Hpow.
  iApply (wpc_idx_mono _ (4 * base ^ (S (S k)))).
  { lia. }
  iApply (wpc_staged_inv_open'' with "[$]"); eauto.
  { transitivity (4 * base ^ (S (S k))); first by lia. rewrite -Hpow. apply Nat.pow_le_mono_r_iff; eauto. lia. }
  { transitivity (base)%nat; first lia. replace base with (base^1) at 1; last by auto.
    apply Nat.pow_lt_mono_r_iff; eauto. lia. }
Qed.

Lemma wpc_later' s k E1 E2 e Φ Φc :
  to_val e = None →
  ▷ ▷ WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }} -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  pose proof (SS_LVL k).
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_later with "[Hwp]"); eauto.
  iNext.
  iApply (wpc_later with "[Hwp]"); eauto.
Qed.

Lemma wpc_later_crash' s k E1 E2 e Φ Φc :
  WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ ▷ ▷ Φc }} -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hwp".
  pose proof (SS_LVL k).
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_later_crash with "[Hwp]"); eauto.
  iApply (wpc_later_crash with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupd' s k E1 E2 e Φ Φc :
  to_val e = None →
  (|={E1}[∅]▷=> WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SS_LVL k) => Hlvl.
  assert (S (LVL k) ≤ LVL (S k)) by lia.
  clear Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_step_fupd with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupdN_inner3 s k E1 E2 e Φ Φc :
  to_val e = None →
  (|={E1,E1}_3=> WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SSS_LVL k) => Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  replace (S (S (S (LVL k)))) with (3 + LVL k) by lia.
  iApply (wpc_step_fupdN_inner with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupdN_inner3_NC s k E1 E2 e Φ Φc :
  to_val e = None →
  Φc ∧ (NC -∗ |={E1,E1}_3=> NC ∗ WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SSS_LVL k) => Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  replace (S (S (S (LVL k)))) with (3 + LVL k) by lia.
  iApply (wpc_step_fupdN_inner_NC with "[Hwp]"); eauto.
  iApply (and_mono with "Hwp"); auto.
  iIntros. by iApply intro_cfupd.
Qed.

Lemma wpc_fupd_crash_shift_empty' s k E1 e Φ Φc :
  WPC e @ s; (LVL k) ; E1 ; ∅ {{ Φ }} {{ |={E1}=> Φc }} ⊢ WPC e @ s; LVL (S k); E1 ; ∅ {{ Φ }} {{ Φc }}.
Proof.
  iApply wpc_fupd_crash_shift_empty.
  rewrite /LVL.
  cut (2 * base ^ (S (S k)) + 1 ≤ base ^ (S (S (S k)))); first lia.
  assert (Hpow: base ^ ((S (S (S k)))) =  base * base ^ (S (S k))).
  { rewrite //=. }
  rewrite Hpow.
  cut (1 ≤ base ^ (S (S k))); first lia.
  replace 1 with (base^0) by auto. apply Nat.pow_le_mono_r_iff; eauto. lia.
Qed.
*)

End staged_inv_wpc.
