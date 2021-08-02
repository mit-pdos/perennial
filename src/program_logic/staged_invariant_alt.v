From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants.
Set Default Proof Using "Type".
Import uPred.

Inductive staged_inv_status :=
| inuse : Qp → Qp → staged_inv_status
| canceled : Qp → staged_inv_status
| idle.

Global Instance staged_inv_status_inhabited : Inhabited staged_inv_status.
Proof. econstructor. apply idle. Qed.

Canonical Structure staged_inv_statusO := leibnizO staged_inv_status.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO gnameO gnameO))));
  staging_status_inG :> inG Σ (authR (optionUR (exclR staged_inv_statusO)));
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition stagedΣ : gFunctors :=
  #[GFunctor (csumR fracR (agreeR unitO));
   GFunctor (authR (optionUR (exclR (prodO gnameO gnameO))));
   GFunctor (authR (optionUR (exclR staged_inv_statusO)));
   savedPropΣ].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* This is the modality guarding the crash condition in a wpc *)
Definition wpc_crash_modality `{!irisGS Λ Σ, !crashG Σ} E1 mj Φc :=
  ((∀ g1 ns D κs,
       let E2 :=  ⊤ ∖ D in
       global_state_interp g1 ns mj D κs -∗ C -∗
     ||={E1|E2,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|E2}=> global_state_interp g1 ns mj D κs ∗ Φc))%I.

Definition wpc_value_modality `{!irisGS Λ Σ, !crashG Σ} E1 mj Φc :=
  ((∀ q g1 ns D κs,
       let E2 :=  ⊤ ∖ D in
       global_state_interp g1 ns mj D κs -∗ NC q -∗
     ||={E1|E2,E1|E2}=> global_state_interp g1 ns mj D κs ∗ Φc ∗ NC q))%I.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

(*
Definition staged_inv_cancel_pre E mj Pc : iProp Σ :=
  ∃ Einv mj_ishare mj_ikeep γ γfinish γstatus,
    ⌜ set_infinite Einv ⌝ ∗
    ⌜ 1 < mj + mj_ikeep ⌝%Qp ∗
    ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
    later_tok ∗
    staged_pending 1 γfinish ∗
    pri_inv_tok mj_ikeep Einv ∗
    pri_inv Einv (staged_inv_inner E Einv mj mj_ishare γ γfinish γstatus Pc).
*)

Definition staged_inv_inner_pre
           (staged_inv_inner : coPset -d> coPset -d> Qp -d> Qp -d> gname -d> gname
                              -d> gname -d> iPropO Σ -d> iPropO Σ) :
           coPset -d> coPset -d> Qp -d> Qp -d> gname -d> gname -d> gname -d> iPropO Σ -d> iPropO Σ :=
          λ E1 E2 mj mj_ishare (γsaved γfinished γstatus: gname) (P: iProp Σ) ,
  ((∃ γprop_stored γprop_remainder (stat: staged_inv_status) Ps Pr,
             own γsaved (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             own γstatus (● Excl' stat) ∗
             pri_inv_tok mj_ishare E2 ∗
             ((match stat with
              | inuse mj_wp mj_ushare => (⌜ (/2) < mj_wp ∧ mj_wp ≤ /2 + mj_ushare ∧ mj_wp ≤ mj ⌝%Qp ∗ Ps ∗ pri_inv_tok mj_ushare E2 ∗ □ (Ps -∗ wpc_crash_modality E1 mj_wp (Pr ∗ P)))
              | canceled mj' => (⌜ (/2) < mj' ≤ mj  ⌝%Qp ∗
                                ∃ E1' Einv mj_ishare mj_ikeep γ γfinish γstatus,
                                  ⌜ E1' ⊆ E1 ⌝ ∗
                                  ⌜ set_infinite Einv ⌝ ∗
                                  ⌜ 1 < mj' + mj_ikeep ⌝%Qp ∗
                                  ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
                                  later_tok ∗
                                  staged_pending 1 γfinish ∗
                                  pri_inv_tok mj_ikeep Einv ∗
                                  pri_inv Einv (staged_inv_inner E1' Einv mj' mj_ishare γ γfinish γstatus P)) ∨
                                  staged_done γfinished
              | idle => (Ps ∧ (C ==∗ P ∗ Pr))
              end)
              ∨
             (Pr ∗ C ∗ (P ∨ staged_done γfinished)))))%I.

Local Instance staged_inv_inner_pre_contractive : Contractive (staged_inv_inner_pre).
Proof.
  rewrite /staged_inv_inner_pre => n pre1 pre2 Hequiv ????????.
  do 15 (f_contractive || f_equiv).
  destruct a1.
  - repeat (f_contractive || f_equiv).
  - do 25 (f_contractive || f_equiv).
    eapply Hequiv.
  - repeat (f_contractive || f_equiv).
Qed.

Definition staged_inv_inner := fixpoint (staged_inv_inner_pre).

Lemma staged_inv_inner_unfold  E1 E2 mj1 mj2 γ1 γ2 γ3 P :
      staged_inv_inner E1 E2 mj1 mj2 γ1 γ2 γ3 P ⊣⊢
      staged_inv_inner_pre staged_inv_inner E1 E2 mj1 mj2 γ1 γ2 γ3 P.
Proof. apply (fixpoint_unfold staged_inv_inner_pre). Qed.

Definition staged_inv E1 E2 (γsaved γfinished γstatus: gname) (P: iProp Σ) : iProp Σ :=
  (∃ mj mj_ishare, ⌜ /2 < mj ⌝%Qp ∗ pri_inv E2 (staged_inv_inner E1 E2 mj mj_ishare γsaved γfinished γstatus P)).

Definition staged_inv_cancel E mj0 Pc : iProp Σ :=
  ∃ mj Einv mj_ishare mj_ikeep γ γfinish γstatus,
    ⌜ /2 < mj ≤ mj0 ⌝%Qp ∗
    ⌜ set_infinite Einv ⌝ ∗
    ⌜ 1 < mj + mj_ikeep ⌝%Qp ∗
    ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
    later_tok ∗
    staged_pending 1 γfinish ∗
    pri_inv_tok mj_ikeep Einv ∗
    pri_inv Einv (staged_inv_inner E Einv mj mj_ishare γ γfinish γstatus Pc).

Definition staged_value_idle E1 (Ps Pr: iProp Σ) P : iProp Σ :=
  (∃ E2 γsaved γfinished γstatus γprop γprop',
      own γsaved (◯ Excl' (γprop, γprop')) ∗
      own γstatus (◯ Excl' idle) ∗
          saved_prop_own γprop Ps ∗
          saved_prop_own γprop' Pr ∗
          later_tok ∗
          pri_inv_tok (/2)%Qp E2 ∗
          staged_inv E1 E2 γsaved γfinished γstatus P)%I.

Definition staged_value E Ps P : iProp Σ := staged_value_idle E Ps True%I P.

End def.

Section inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{PRI: !pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

(* TODO: this is annoying but true *)
(*
Global Instance staged_contractive  E γ γ' : Contractive (staged_inv E γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  rewrite pri_inv_full_eq /pri_inv_full_def.
  f_equiv => ?.
  rewrite pri_inv_eq /pri_inv_def.
  do 4 f_equiv.
Qed.

Global Instance staged_ne N k E E' γ γ': NonExpansive (staged_inv N k E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto using dist_le.
Qed.

Global Instance staged_proper N k E E' γ γ' : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N k E E' γ γ').
Proof. apply ne_proper, _. Qed.
*)

Global Instance staged_persistent E1 E2 γ1 γ2 γ3 P : Persistent (staged_inv E1 E2 γ1 γ2 γ3 P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done q γ: staged_pending q γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending 1%Qp γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending 1 γ.
Proof.
  iApply (own_alloc (Cinl 1%Qp)).
  { rewrite //=. }
Qed.

Lemma pending_split γ:
  staged_pending 1 γ ⊢ staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma pending_split34 γ:
  staged_pending 1 γ ⊢ staged_pending (3/4)%Qp γ ∗ staged_pending (1/4)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_three_quarter_quarter. Qed.

Lemma pending_join γ:
 staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma pending_join34 γ:
 staged_pending (3/4)%Qp γ ∗ staged_pending (1/4)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_three_quarter_quarter. Qed.

Lemma pending34_pending34 γ:
 staged_pending (3/4)%Qp γ -∗ staged_pending (3/4)%Qp γ -∗ False.
Proof.
  rewrite /staged_pending.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_pending γ:
 staged_pending 1%Qp γ -∗ staged_pending 1%Qp γ -∗ False.
Proof.
  rewrite /staged_pending.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

(* TODO : *)
(*
Lemma staged_inv_iff E i γ γ' P Q :
  ▷ □ (P ↔ Q) -∗
  staged_inv E i γ γ' P -∗
  staged_inv E i γ γ' Q.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
Qed.
*)

Lemma wpc_crash_modality_intro_C E mj P :
  (C -∗ wpc_crash_modality E mj P) -∗
  wpc_crash_modality E mj P.
Proof.
  iIntros "H". rewrite /wpc_crash_modality.
  iIntros. iApply ("H" with "[$] [$] [$]").
Qed.

Lemma wpc_crash_modality_strong_wand E1 E2 mj1 mj2 P Q :
  E1 ⊆ E2 →
  (/2 < mj1 ≤ mj2)%Qp →
  wpc_crash_modality E1 mj1 P -∗
  (P ={E2}=∗ Q) -∗
  wpc_crash_modality E2 mj2 Q.
Proof using PRI.
  iIntros (??) "Hwpc Hwand".
  rewrite /wpc_crash_modality.
  iIntros (g1 ns D κs) "Hg #C".
  iApply (step_fupd2N_inner_fupd2).
  iDestruct (pri_inv_tok_global_le_acc with "[//] Hg") as "(Hg&Hg_clo)".
  iSpecialize ("Hwpc" with "[$] [$]").
  iApply (step_fupd2N_inner_wand with "Hwpc"); auto.
  iIntros "(Hg&HP)". iDestruct ("Hg_clo" with "[$Hg]") as "$".
  by iMod ("Hwand" with "[$]") as "$".
Qed.

Lemma wpc0_modality_postcondition_cancel_atomic s k mj E e Φ Φc `{!Atomic StronglyAtomic e}:
  (wpc0 s k mj E e Φ Φc) -∗
  (wpc0 s k mj E e (λ v, wpc_crash_modality E mj Φc ∧ (wpc_value_modality E mj (Φ v))) Φc).
Proof.
  iIntros "H".
  rewrite ?wpc0_unfold. rewrite /wpc_pre.
  iSplit; last first.
  { iDestruct "H" as "(_&H)". eauto. }
  destruct (to_val e).
  - iIntros (q g1 ns D κs) "Hg HNC".
    iFrame. iModIntro.
    iSplit.
    { iDestruct "H" as "(_&H)".
      iIntros (????) "Hg HC".
      iSpecialize ("H" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "H"); auto.
    }
    { iDestruct "H" as "(H&_)".
      rewrite /wpc_value_modality. iIntros.
      iSpecialize ("H" with "[$] [$]").
      iMod (fupd2_mask_subseteq E (⊤ ∖ _)) as "Hclo".
      { auto. }
      { reflexivity. }
      iMod "H" as "($&$&$)". iMod "Hclo"; eauto. }
  - iIntros.
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$]") as "H". iModIntro.
    simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "($&H)".
    iIntros.
    iMod ("H" with "[//]") as "($&$&H&$)".
    iModIntro.
    rewrite /Atomic/= in Atomic0.
    edestruct (Atomic0) as (v&Hval); eauto.
    rewrite Hval. rewrite ?wpc0_unfold /wpc_pre.
    rewrite Hval. iSplit; last first.
    { iDestruct "H" as "(_&H)". eauto. }
    iIntros. iModIntro. iFrame.
    iSplit.
    { iDestruct "H" as "(_&H)".
      iIntros (????) "Hg HC".
      iSpecialize ("H" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "H"); auto.
    }
    { iDestruct "H" as "(H&_)".
      rewrite /wpc_value_modality. iIntros.
      iSpecialize ("H" with "[$] [$]").
      iMod (fupd2_mask_subseteq E (⊤ ∖ _)) as "Hclo".
      { auto. }
      { reflexivity. }
      iMod "H" as "($&$&$)". iMod "Hclo"; eauto. }
Qed.

Lemma wpc0_modality_postcondition_cancel s k mj E e Φ Φc :
  (wpc0 s k mj E e Φ Φc) -∗
  (wpc0 s k mj E e (λ v, wpc_crash_modality ⊤ mj Φc ∧ (wpc_value_modality ⊤ mj (Φ v))) Φc).
Proof.
  iIntros "H".
  iLöb as "IH" forall (e E).
  rewrite ?wpc0_unfold. rewrite /wpc_pre.
  iSplit; last first.
  { iDestruct "H" as "(_&H)". eauto. }
  destruct (to_val e).
  - iIntros (q g1 ns D κs) "Hg HNC".
    iFrame. iModIntro.
    iSplit.
    { iDestruct "H" as "(_&H)".
      iIntros (????) "Hg HC".
      iSpecialize ("H" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "H"); auto.
    }
    { iDestruct "H" as "(H&_)".
      rewrite /wpc_value_modality. iIntros.
      iSpecialize ("H" with "[$] [$]").
      iMod (fupd2_mask_subseteq E (⊤ ∖ _)) as "Hclo".
      { auto. }
      { reflexivity. }
      iMod "H" as "($&$&$)". iMod "Hclo"; eauto. }
  - iIntros.
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$]") as "H". iModIntro.
    simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "($&H)".
    iIntros.
    iMod ("H" with "[//]") as "($&$&H&$)".
    iModIntro. by iApply "IH".
Qed.

Lemma wpc_crash_modality_intro E1 mj P :
  P -∗ wpc_crash_modality E1 mj P.
Proof.
  iIntros "H".
  rewrite /wpc_crash_modality.
  iIntros (g1 ns D κs) "Hg #C".
  iApply (step_fupd2N_inner_later); auto.
  iNext. iFrame.
Qed.

Lemma wpc_crash_modality_wand E1 mj P Q :
  wpc_crash_modality E1 mj P -∗
  (P ={E1}=∗ Q) -∗
  wpc_crash_modality E1 mj Q.
Proof.
  iIntros "Hwpc Hwand".
  rewrite /wpc_crash_modality.
  iIntros (g1 ns D κs) "Hg #C".
  iApply (step_fupd2N_inner_fupd2).
  iSpecialize ("Hwpc" with "[$] [$]").
  iApply (step_fupd2N_inner_wand with "Hwpc"); auto.
  iIntros "($&HP)". by iMod ("Hwand" with "[$]") as "$".
Qed.

Lemma wpc_crash_modality_combine E1 mj P1 P2 :
  later_tok -∗
  ▷ wpc_crash_modality E1 mj P1 -∗
  ▷ wpc_crash_modality E1 mj P2 -∗
  wpc_crash_modality E1 mj (P1 ∗ P2).
Proof.
  iIntros "Htok H1 H2".
  rewrite /wpc_crash_modality.
  iIntros (g1 ns D κs) "Hg #C".
  iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
  iApply (step_fupd2N_inner_fupd2).
  iApply (step_fupd2N_inner_le).
  { apply (num_laters_per_step_exp ns'). lia. }
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iEval (simpl).
  do 2 (iModIntro; iModIntro; iNext).
  iMod "Hclo'".
  iApply step_fupd2N_inner_plus.
  iSpecialize ("H1" with "[$] [$]").
  iApply (step_fupd2N_inner_wand with "H1"); auto.
  iIntros "(Hg&HP1)".
  iSpecialize ("H2" with "[$] [$]").
  iApply (step_fupd2N_inner_wand with "H2"); auto.
  iIntros "(Hg&$)".
  iMod (global_state_interp_le with "[$]") as "$"; auto. lia.
Qed.

Lemma wpc_crash_modality_split E Einv mj1 mj2 P1 P2 :
  (/2 < mj1 < mj2)%Qp →
  later_tok -∗
  later_tok -∗
  pri_inv_tok 1%Qp Einv -∗
  wpc_crash_modality E mj1 (P1 ∗ P2) -∗
  ||={∅|∅, ∅|∅}=> wpc_crash_modality E mj2 P1 ∗ wpc_crash_modality E mj2 P2.
Proof using stagedG0.
  destruct (decide (mj2 ≤ 1)%Qp) as [Hle|Hnle]; last first.
  { iIntros. iModIntro.
    iSplitL.
    - iIntros (????) "Hg HC".
      iDestruct (pri_inv_tok_global_valid with "[$]") as %(?&?).
      exfalso. naive_solver.
    - iIntros (????) "Hg HC".
      iDestruct (pri_inv_tok_global_valid with "[$]") as %(?&?).
      exfalso. naive_solver.
  }
  iIntros (Hlt) "Hltok Hltok2 H".
  iIntros "Hg".
  destruct (Qp_plus_split_alt mj1 mj2) as (qa&qb&Hle1&Hlt2&Hle3); auto.
  rewrite -Hle1.
  iDestruct (pri_inv_tok_split with "H") as "(Hqa&Hqb)".
  iDestruct (pri_inv_tok_split with "Hqa") as "(Hqa1&Hqa2)".
  iMod (pending_alloc) as (γ1) "H1".
  iMod (pending_alloc) as (γ2) "H2".
  iDestruct (pri_inv_tok_infinite with "Hqb") as %Hinf.
  iMod (pri_inv_alloc Einv _ _
                      (pri_inv_tok qb Einv ∗ (wpc_crash_modality E mj1 (P1 ∗ P2) ∨
                                              ((P1 ∨ staged_done γ1) ∗ (P2 ∨ staged_done γ2)))) with "[$Hqb $Hg]")
  as "#Hinv"; first done.
  iModIntro.
  iSplitL "Hltok Hqa1 H1".
  {
    rewrite /wpc_crash_modality.
    iIntros.
    iMod (later_tok_decr with "[$]") as (ns' Hle') "Hg".
    iApply (step_fupd2N_inner_fupd2).
    iApply (step_fupd2N_inner_le _ (S (num_laters_per_step ns'))).
    { apply lt_le_S. apply (num_laters_per_step_lt). lia. }
    simpl.
    iDestruct (pri_inv_tok_disj with "[$]") as %[Hdisj|Hval]; last first.
    { exfalso. apply Qp_lt_nge in Hlt2. revert Hval. rewrite frac_valid.
      intros HleX. apply Hlt2. etransitivity; last eassumption.
      apply Qp_add_le_mono_r. auto. }
    iMod (pri_inv_acc with "Hinv") as "(Hinner&Hclo)".
    { set_solver. }
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    iModIntro. iModIntro. iNext. iMod "Hclo'".
    iDestruct "Hinner" as "(Htok&Hcases)".
    iDestruct "Hcases" as "[Hunrun|Hrun]".
    {
      iDestruct (pri_inv_tok_join with "Hqa1 Htok") as "Hitok'".
      iDestruct (pri_inv_tok_le_acc mj1 with "[$]") as "(Hitok&Hitok_clo)".
      { auto. }
      iDestruct (pri_inv_tok_global_le_acc _ _ _ mj1 with "[] Hg") as "(Hg&Hg_clo)".
      { iPureIntro. split; first naive_solver.
        apply Qp_lt_le_incl; naive_solver. }
      iMod (pri_inv_tok_disable with "[$Hg $Hitok]") as "Hg".
      replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
      iSpecialize ("Hunrun" with "[$] [$]").
      iMod "Hunrun".  iModIntro. iApply (step_fupd2N_wand with "Hunrun").
      iIntros "Hunrun". iMod "Hunrun" as "(Hg&HP1&HP2)".
      iMod (pending_upd_done with "H1") as "Hdone".
      iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
      iDestruct ("Hitok_clo" with "[$]") as "Hitok".
      iDestruct (pri_inv_tok_split with "[$]") as "(Hitok1&Hitok2)".
      iMod ("Hclo" with "[Hitok2 HP2 Hdone]").
      { iFrame. iNext. iRight. iFrame. }
      iModIntro.
      iDestruct ("Hg_clo" with "[$]") as "Hg_clo".
      iMod (global_state_interp_le with "[$]") as "$".
      { lia. }
      eauto.
    }
    iDestruct "Hrun" as "(Hrun1&Hrun2)".
    iDestruct "Hrun1" as "[HP1|Hfalse]"; last first.
    { iDestruct (pending_done with "[$] [$]") as %[]. }
    iMod (pending_upd_done with "H1") as "Hdone".
    iMod ("Hclo" with "[Hdone Hrun2 Htok]").
    { iFrame. iRight. iNext. iFrame. }

    iApply (step_fupd2N_inner_later); auto. iModIntro.
    iMod (global_state_interp_le with "[$]") as "$".
    { lia. }
    iFrame. eauto.
  }
  {
    rewrite /wpc_crash_modality.
    iIntros.
    iMod (later_tok_decr with "[$]") as (ns' Hle') "Hg".
    iApply (step_fupd2N_inner_fupd2).
    iApply (step_fupd2N_inner_le _ (S (num_laters_per_step ns'))).
    { apply lt_le_S. apply (num_laters_per_step_lt). lia. }
    simpl.
    iDestruct (pri_inv_tok_disj with "[$]") as %[Hdisj|Hval]; last first.
    { exfalso. apply Qp_lt_nge in Hlt2. revert Hval. rewrite frac_valid.
      intros HleX. apply Hlt2. etransitivity; last eassumption.
      apply Qp_add_le_mono_r. auto. }
    iMod (pri_inv_acc with "Hinv") as "(Hinner&Hclo)".
    { set_solver. }
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    iModIntro. iModIntro. iNext. iMod "Hclo'".
    iDestruct "Hinner" as "(Htok&Hcases)".
    iDestruct "Hcases" as "[Hunrun|Hrun]".
    {
      iDestruct (pri_inv_tok_join with "Hqa2 Htok") as "Hitok'".
      iDestruct (pri_inv_tok_le_acc mj1 with "[$]") as "(Hitok&Hitok_clo)".
      { auto. }
      iDestruct (pri_inv_tok_global_le_acc _ _ _ mj1 with "[] Hg") as "(Hg&Hg_clo)".
      { iPureIntro. split; first naive_solver.
        apply Qp_lt_le_incl; naive_solver. }
      iMod (pri_inv_tok_disable with "[$Hg $Hitok]") as "Hg".
      replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
      iSpecialize ("Hunrun" with "[$] [$]").
      iMod "Hunrun".  iModIntro. iApply (step_fupd2N_wand with "Hunrun").
      iIntros "Hunrun". iMod "Hunrun" as "(Hg&HP1&HP2)".
      iMod (pending_upd_done with "H2") as "Hdone".
      iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
      iDestruct ("Hitok_clo" with "[$]") as "Hitok".
      iDestruct (pri_inv_tok_split with "[$]") as "(Hitok1&Hitok2)".
      iMod ("Hclo" with "[Hitok2 HP1 Hdone]").
      { iFrame. iNext. iRight. iFrame. }
      iModIntro.
      iDestruct ("Hg_clo" with "[$]") as "Hg_clo".
      iMod (global_state_interp_le with "[$]") as "$".
      { lia. }
      eauto.
    }
    iDestruct "Hrun" as "(Hrun1&Hrun2)".
    iDestruct "Hrun2" as "[HP2|Hfalse]"; last first.
    { iDestruct (pending_done with "[$] [$]") as %[]. }
    iMod (pending_upd_done with "H2") as "Hdone".
    iMod ("Hclo" with "[Hdone Hrun1 Htok]").
    { iFrame. iRight. iNext. iFrame. }

    iApply (step_fupd2N_inner_later); auto. iModIntro.
    iMod (global_state_interp_le with "[$]") as "$".
    { lia. }
    iFrame. eauto.
  }
Qed.

End inv.
