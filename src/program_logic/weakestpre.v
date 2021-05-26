From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require Export language weakestpre_notation crash_weakestpre.
From iris.prelude Require Import options.
Import uPred.

Section wp.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof. rewrite wp_eq=>???. by eapply wpc_ne. Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
(*Global Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 17 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 15 f_equiv.
Qed.*)

(*
Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |NC={E}=> Φ v.
Proof.
  rewrite wp_eq /wp_def. iSplit.
  - rewrite ncfupd_eq /ncfupd_def.
    iIntros "Hwp" (q). iApply wpc_value_inv'. done.
  - iIntros "HΦ". iApply ncfupd_wpc. iSplit; first done.
    iMod "HΦ". iApply wpc_value'. eauto.
Qed.

Lemma wp_value_fupd'_1 s E Φ v : WP of_val v @ s; E {{ Φ }} ⊢ |NC={E}=> Φ v.
Proof. rewrite wp_value_fupd' //. Qed.
*)

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v -∗ |NC={E2}=> Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". rewrite wp_eq.
  iApply (wpc_strong_mono with "H"); eauto.
Qed.

Lemma ncfupd_wp s E e Φ : (|NC={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp". rewrite wp_eq. iApply ncfupd_wpc.
  iSplit; first by eauto. done.
Qed.
Lemma fupd_wp s E e Φ : (|={E}=> (WP e @ s; E {{ Φ }})) ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply ncfupd_wp. iMod "H". eauto. Qed.
Lemma wp_ncfupd s E e Φ : WP e @ s; E {{ v, |NC={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, fupd E E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. by iIntros (v) ">H". Qed.

Lemma wp_ncatomic s E1 E2 e Φ `{!Atomic StronglyAtomic e} :
  (|NC={E1,E2}=> WP e @ s; E2 {{ v, |NC={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite wp_eq /wp_def !wpc_unfold /wpc_pre.
  rewrite ncfupd_eq /ncfupd_def. iIntros (mj).
  iSplit; last first.
  { iIntros. iApply step_fupd_extra.step_fupd2N_inner_later; [done|done|]. iNext; iFrame. }
  destruct (to_val e) as [v|] eqn:He.
  { iIntros (q ????) "Hg HNC". iMod ("H" with "[$]") as "(H&HNC)".
    iDestruct ("H" $! mj) as "[H _]".
    iMod ("H" with "[$] [$]") as "(H&Hg&HNC)". iMod ("H" with "[$]") as "(H&HNC)". by iFrame.
  }
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iMod ("H" with "[$]") as "(H&HNC)".
  iDestruct ("H" $! mj) as "[H _]".
  iMod ("H" $! _ σ1 with "Hσ Hg [$]") as "H". iModIntro.
  iApply (step_fupd_extra.step_fupd2N_wand with "H").
  iIntros "[% H]". iSplit; first done.
  iIntros (e2 σ2 g2 efs Hstep).
  iMod ("H" with "[//]") as "($ & Hg & H & $ & HNC)".
  - destruct (atomic _ _ _ _ _ _ _ Hstep) as [v <-%of_to_val].
    iDestruct (wpc0_value_inv' with "H") as "H".
    rewrite to_of_val.
    iMod ("H" with "[$] [$]") as "(H&Hg&HNC)".
    iMod ("H" with "[$]") as "(H&HNC)".
    iModIntro. iFrame. rewrite wpc0_unfold /wpc_pre.
    rewrite to_of_val /=. iSplit; last first.
    { iIntros. iApply step_fupd_extra.step_fupd2N_inner_later; [done|done|]. iNext; iFrame. }
    iIntros (?????) "$ $". done.
Qed.
Lemma wp_atomic s E1 E2 e Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply wp_ncatomic; auto. iMod "H". iModIntro. iApply (wp_strong_mono with "H"); eauto.
  iIntros (?) "H". iModIntro. iMod "H". eauto.
Qed.

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
(* FIXME(RJ) we should probably have such a lemma for WPC and apply that here *)
Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ g ns mj D κs nt, state_interp σ nt -∗ global_state_interp g ns mj D κs
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H".
    iMod "HP" as ">HP". iMod ("H" with "HP"). done. }
  rewrite wp_eq /wp_def !wpc_unfold /wpc_pre /=.
  iIntros (-> ?) "H". iIntros (mj).
  iSplit; last first.
  { iIntros. iApply step_fupd_extra.step_fupd2N_inner_later; [done|done|]. iNext; iFrame. }
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ Hg") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iDestruct ("Hwp" $! mj) as "[Hwp _]".
  iMod ("Hwp" with "Hσ Hg [$]") as "H".
  iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupd_extra.step_fupd2N_wand with "H").
    iIntros "!> [$ H]". iIntros.
    iMod "HP". simpl. iMod ("H" with "[//]") as "($ & $ & Hwp & $)". iMod "HP".
    iModIntro. iApply (wpc0_strong_mono with "Hwp"); auto.
    { destruct (to_val _); eauto. }
    iSplit; last by auto.
    iIntros (v) "HΦ".
    iApply (ncfupd_mask_mono); last by iMod ("HΦ" with "[$]").
    { destruct (to_val _); eauto. }
  - destruct n0 as [|n0]; [lia|]=>/=.
    iMod "H".
    iModIntro. iNext. iMod "HP". iMod "H".
    iSpecialize ("IH" with "[] HP H"); first auto with lia.
    iMod "IH". iModIntro. eauto.
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". rewrite wp_eq /wp_def.
  iApply wpc_bind. done.
Qed.

(*
Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iIntros (q) "HNC".
    rewrite !wp_unfold /wp_pre. iModIntro. iFrame. }
  rewrite fill_not_val //.
  iIntros (q σ1 ns κ κs nt) "Hσ HNC".
  iMod ("H" with "[$] [$]") as "H".
  iModIntro. iApply (step_fupdN_wand with "H"). iNext.
  iIntros "[% H]".
  iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! _ _ _ with "[]") as "H"; first eauto using fill_step.
  iIntros "!>". iDestruct "H" as "($ & H & $)". by iApply "IH".
Qed.
*)

(** * Derived rules *)
(* wp_mono is in crash_weakestpre *)
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

(*
Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |NC={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
*)
Lemma wp_value_fupd s E Φ e v : IntoVal e v → (|NC={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  intros <-. iIntros "HΦ".
  rewrite wp_eq /wp_def.
  iApply ncfupd_wpc. iSplit; first done.
  iMod "HΦ". iApply wpc_value'. eauto.
Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. iIntros "H". iApply wp_value_fupd; auto. done. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame.
Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame.
Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the WP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma wp_step_fupdN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ g ns mj D κs nt, state_interp σ nt -∗ global_state_interp g ns mj D κs
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
  iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (???????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R : R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_ncfupd_wp p s E e P Φ :
    ElimModal True p false (|NC={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      ncfupd_frame_r wand_elim_r ncfupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_ncfupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false (|NC={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |NC={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite /ElimModal intuitionistically_if_elim
      ncfupd_frame_r wand_elim_r wp_ncatomic.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic; eauto.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_ncfupd_wp {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e) (ncfupd E1 E2) (ncfupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |NC={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_ncfupd_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (ncfupd E E) (ncfupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |NC={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc /accessor.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_ncfupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
