From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Export fancy_updates crash_token.
From Perennial.base_logic.lib Require Import wsat.
From iris.prelude Require Import options.
Import uPred.


Definition ncfupd_def `{!invG Σ, !crashG Σ} (E1 E2 : coPset) (P: iProp Σ) : iProp Σ :=
  ∀ q, NC q -∗ |={E1, E2}=> P ∗ NC q.
Definition ncfupd_aux `{!invG Σ, !crashG Σ} : seal (ncfupd_def). Proof. by eexists. Qed.
Definition ncfupd `{!invG Σ, !crashG Σ} := ncfupd_aux.(unseal).
Definition ncfupd_eq `{!invG Σ, !crashG Σ} : ncfupd = ncfupd_def := ncfupd_aux.(seal_eq).

Notation "|NC={ E1 }=> Q" := (ncfupd E1 E1 Q)
  (at level 99, E1 at level 50, Q at level 200,
   format "|NC={ E1 }=>  Q") : bi_scope.
Notation "|NC={ E1 , E2 }=> P" := (ncfupd E1 E2 P)
      (at level 99, E1, E2 at level 50, P at level 200,
       format "|NC={ E1 , E2 }=>  P") : bi_scope.
Notation "|NC={ Eo } [ Ei ]▷=> Q" := (∀ q, NC q -∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> Q ∗ NC q)%I
  (at level 99, Eo, Ei at level 50, Q at level 200,
   format "|NC={ Eo } [ Ei ]▷=>  Q") : bi_scope.
Notation "|NC={ E1 } [ E2 ]▷=>^ n Q" := (Nat.iter n (λ P, |NC={E1}[E2]▷=> P) Q)%I
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
   format "|NC={ E1 } [ E2 ]▷=>^ n  Q").

Section ncfupd.
Context `{!invG Σ, !crashG Σ}.
Implicit Types P: iProp Σ.
Implicit Types E : coPset.

Global Instance ncfupd_ne E1 E2 : NonExpansive (ncfupd E1 E2).
Proof. rewrite ncfupd_eq. solve_proper. Qed.

Lemma ncfupd_intro_mask E1 E2 P : E2 ⊆ E1 → P ⊢ |NC={E1,E2}=> |NC={E2,E1}=> P.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  iIntros (?) "HP". iIntros (q) "HNC".
  iMod fupd_mask_subseteq as "Hclo"; try eassumption. iModIntro.
  iFrame "HNC". iIntros.
  iMod "Hclo". by iFrame.
Qed.

Lemma except_0_ncfupd E1 E2 P : ◇ (|NC={E1,E2}=> P) ⊢ |NC={E1,E2}=> P.
Proof. rewrite ncfupd_eq. iIntros "H". iIntros (q) "HNC". iMod "H". by iApply "H". Qed.

Lemma ncfupd_mono E1 E2 P Q : (P ⊢ Q) → (|NC={E1,E2}=> P) ⊢ |NC={E1,E2}=> Q.
Proof.
  rewrite ncfupd_eq.
  iIntros (HPQ) "H". iIntros (q) "HNC". iMod ("H" with "[$]") as "(?&$)".
  iModIntro. by iApply HPQ.
Qed.

Lemma fupd_ncfupd E1 E2 P : (|={E1,E2}=> P) ⊢ |NC={E1,E2}=> P.
Proof.
  rewrite ?ncfupd_eq. iIntros "H". iIntros (q) "HNC". iMod "H" as "$". eauto.
Qed.

Lemma ncfupd_trans E1 E2 E3 P : (|NC={E1,E2}=> |NC={E2,E3}=> P) ⊢ |NC={E1,E3}=> P.
Proof.
  rewrite ?ncfupd_eq. iIntros "H". iIntros (q) "HNC".
  iMod ("H" with "[$]") as "(H&HNC)".
  iMod ("H" with "[$]") as "($&$)".
  eauto.
Qed.

Lemma ncfupd_mask_frame_r' E1 E2 Ef P:
    E1 ## Ef → (|NC={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |NC={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  rewrite ?ncfupd_eq. iIntros (?) "H". iIntros (q) "HNC".
  iSpecialize ("H" with "[$]"). iApply (fupd_mask_frame_r'); eauto.
  iMod "H" as "(H&?)". iIntros "!> ?". iFrame. by iApply "H".
Qed.

Lemma ncfupd_frame_r E1 E2 P R:
  (|NC={E1,E2}=> P) ∗ R ⊢ |NC={E1,E2}=> P ∗ R.
Proof.
  rewrite ncfupd_eq.
  iIntros "(H&$)". iIntros (q) "HNC". by iMod ("H" with "[$]").
Qed.

Global Instance ncfupd_proper E1 E2 :
  Proper ((≡) ==> (≡)) (ncfupd E1 E2) := ne_proper _.


Global Instance ncfupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (ncfupd E1 E2).
Proof. intros P Q; apply ncfupd_mono. Qed.
Global Instance ncfupd_flip_mono' E1 E2 :
  Proper (flip (⊢) ==> flip (⊢)) (ncfupd E1 E2).
Proof. intros P Q; apply ncfupd_mono. Qed.

Lemma bupd_ncfupd E P:
  (|==> P) ⊢ |NC={E}=> P.
Proof.
  rewrite ncfupd_eq.
  iIntros "H". iIntros (q) "HNC".
  iMod "H".  by iFrame.
Qed.

Lemma ncfupd_intro E P : P ⊢ |NC={E}=> P.
Proof. by rewrite {1}(ncfupd_intro_mask E E P) // ncfupd_trans. Qed.
(** [iMod (ncfupd_mask_subseteq E)] is the recommended way to change your
current mask to [E]. *)
Lemma ncfupd_mask_subseteq {E1} E2 : E2 ⊆ E1 → ⊢@{iPropI Σ} |NC={E1,E2}=> |NC={E2,E1}=> emp.
Proof. exact: ncfupd_intro_mask. Qed.
Lemma ncfupd_except_0 E1 E2 P : (|NC={E1,E2}=> ◇ P) ⊢ |NC={E1,E2}=> P.
Proof. by rewrite {1}(ncfupd_intro E2 P) except_0_ncfupd ncfupd_trans. Qed.

Global Instance from_assumption_ncfupd E p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|NC={E}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_ncfupd. Qed.

Global Instance from_pure_ncfupd a E P φ :
  FromPure a P φ → FromPure a (|NC={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply ncfupd_intro. Qed.

Lemma ncfupd_frame_l E1 E2 R Q : (R ∗ |NC={E1,E2}=> Q) ⊢ |NC={E1,E2}=> R ∗ Q.
Proof. rewrite !(comm _ R); apply ncfupd_frame_r. Qed.
Lemma ncfupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|NC={E1,E2}=> P) ⊢ |NC={E1,E2}=> Q.
Proof. by rewrite ncfupd_frame_l wand_elim_l. Qed.
Lemma ncfupd_wand_r E1 E2 P Q : (|NC={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |NC={E1,E2}=> Q.
Proof. by rewrite ncfupd_frame_r wand_elim_r. Qed.

Lemma ncfupd_mask_weaken E1 E2 P : E2 ⊆ E1 → P ⊢ |NC={E1,E2}=> P.
Proof.
  intros ?. rewrite -{1}(right_id emp%I bi_sep P%I).
  rewrite (ncfupd_intro_mask E1 E2 emp%I) //.
  by rewrite ncfupd_frame_l sep_elim_l.
Qed.

Lemma ncfupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → (|NC={E1,E2}=> P) ⊢ |NC={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros ?. rewrite -ncfupd_mask_frame_r' //. f_equiv.
  apply impl_intro_l, and_elim_r.
Qed.
Lemma ncfupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|NC={E1}=> P) ⊢ |NC={E2}=> P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply ncfupd_mask_frame_r.
Qed.

Lemma ncfupd_sep E P Q : (|NC={E}=> P) ∗ (|NC={E}=> Q) ⊢ |NC={E}=> P ∗ Q.
Proof. by rewrite ncfupd_frame_r ncfupd_frame_l ncfupd_trans. Qed.
Lemma ncfupd_mask_frame E E' E1 E2 P :
  E1 ⊆ E →
  (|NC={E1,E2}=> |NC={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|NC={E,E'}=> P).
Proof.
  intros ?. rewrite (ncfupd_mask_frame_r _ _ (E ∖ E1)); last set_solver.
  rewrite ncfupd_trans.
  by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
Qed.

Global Instance into_wand_ncfupd E p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|NC={E}=> R) (|NC={E}=> P) (|NC={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite ncfupd_sep wand_elim_r.
Qed.

Global Instance into_wand_ncfupd_persistent E1 E2 p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|NC={E1,E2}=> R) P (|NC={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite ncfupd_frame_l wand_elim_r.
Qed.

Global Instance into_wand_ncfupd_args E1 E2 p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|NC={E1,E2}=> P) (|NC={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim ncfupd_wand_r.
Qed.

Global Instance from_sep_ncfupd E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|NC={E}=> P) (|NC={E}=> Q1) (|NC={E}=> Q2).
Proof. rewrite /FromSep =><-. apply ncfupd_sep. Qed.

Global Instance from_or_ncfupd E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|NC={E1,E2}=> P) (|NC={E1,E2}=> Q1) (|NC={E1,E2}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply ncfupd_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_exist_ncfupd {A} E1 E2 P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (|NC={E1,E2}=> P) (λ a, |NC={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

Lemma ncfupd_plain_forall_2 E {A} (Φ : A → iProp Σ) `{!∀ x, Plain (Φ x)} :
  (∀ x, |NC={E}=> Φ x) ⊢ |NC={E}=> ∀ x, Φ x.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "H" (q) "HNC".
  iIntros "[Hw HE]".
  iAssert (◇ ∀ x : A, Φ x)%I as "#>HP".
  { iIntros (x). by iMod ("H" $! x q with "[$] [$Hw $HE]") as "(_&_&?&?)". }
  iFrame. eauto.
Qed.

Lemma ncfupd_plainly_mask_empty E P : (|NC={E,∅}=> ■ P) ⊢ |NC={E}=> P.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  iIntros "H". iIntros (q) "HNC".
  iSpecialize ("H" $! q).
  iApply fupd_plainly_keep_l. iFrame.
  iIntros "HNC". iSpecialize ("H" with "[$]").
  iApply (fupd_plain_mask_empty). by iMod "H" as "($&_)".
Qed.

Lemma ncfupd_plain_mask_empty E P `{!Plain P} : (|NC={E,∅}=> P) ⊢ |NC={E}=> P.
Proof. by rewrite {1}(plain P) ncfupd_plainly_mask_empty. Qed.

Lemma ncfupd_elim E1 E2 E3 P Q :
  (Q -∗ (|NC={E2,E3}=> P)) → (|NC={E1,E2}=> Q) -∗ (|NC={E1,E3}=> P).
Proof. intros ->. rewrite ncfupd_trans //. Qed.

Lemma ncfupd_plainly_mask E E' P : (|NC={E,E'}=> ■ P) ⊢ |NC={E}=> P.
Proof.
  rewrite -(ncfupd_plainly_mask_empty).
  apply ncfupd_elim, (ncfupd_mask_weaken _ _ _). set_solver.
Qed.

Lemma ncfupd_plain_mask E E' P `{!Plain P} : (|NC={E,E'}=> P) ⊢ |NC={E}=> P.
Proof. by rewrite {1}(plain P) ncfupd_plainly_mask. Qed.

Lemma ncfupd_plainly_elim E P : ■ P -∗ |NC={E}=> P.
Proof. by rewrite (ncfupd_intro E (■ P)%I) ncfupd_plainly_mask. Qed.

Lemma ncfupd_plain_fupd E P  `{!Plain P} : (∀ q, NC q -∗ |={E}=> P) -∗ |NC={E}=> P.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  iIntros "H" (q) "HNC". iApply (fupd_plain_keep_l). iFrame.
  iApply "H".
Qed.

Lemma ncfupd_plain_forall E1 E2 {A} (Φ : A → iProp Σ) `{!∀ x, Plain (Φ x)} :
  E2 ⊆ E1 →
  (|NC={E1,E2}=> ∀ x, Φ x) ⊣⊢ (∀ x, |NC={E1,E2}=> Φ x).
Proof.
  intros. apply (anti_symm _).
  { apply forall_intro=> x. by rewrite (forall_elim x). }
  trans (∀ x, |NC={E1}=> Φ x)%I.
  { apply forall_mono=> x. by rewrite ncfupd_plain_mask. }
  rewrite ncfupd_plain_forall_2. apply ncfupd_elim.
  rewrite {1}(plain (∀ x, Φ x)) (ncfupd_mask_weaken E1 E2 (■ _)%I) //.
  apply ncfupd_elim. by rewrite ncfupd_plainly_elim.
Qed.

Global Instance from_forall_ncfupd E1 E2 {A} P (Φ : A → iProp Σ) name :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ name → (∀ x, Plain (Φ x)) →
  FromForall (|NC={E1,E2}=> P)%I (λ a, |NC={E1,E2}=> (Φ a))%I name.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite ncfupd_plain_forall; set_solver.
Qed.

Global Instance except_0_ncfupd' E1 E2 P :
  IsExcept0 (|NC={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_ncfupd. Qed.

Global Instance from_modal_ncfupd E P :
  FromModal modality_id (|NC={E}=> P) (|NC={E}=> P) P.
Proof. by rewrite /FromModal /= -ncfupd_intro. Qed.

Global Instance elim_modal_bupd_ncfupd p E1 E2 P Q :
  ElimModal True p false (|==> P) P (|NC={E1,E2}=> Q) (|NC={E1,E2}=> Q) | 10.
Proof.
   by rewrite /ElimModal intuitionistically_if_elim
    (bupd_ncfupd E1) ncfupd_frame_r wand_elim_r ncfupd_trans.
Qed.
Global Instance elim_modal_ncfupd_ncfupd p E1 E2 E3 P Q :
  ElimModal True p false (|NC={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    ncfupd_frame_r wand_elim_r ncfupd_trans.
Qed.

Global Instance elim_modal_fupd_ncfupd p E1 E2 E3 P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
Proof.
  rewrite /ElimModal => ?. rewrite (fupd_ncfupd _ _) intuitionistically_if_elim
    ncfupd_frame_r wand_elim_r ncfupd_trans //=.
Qed.

Global Instance add_modal_ncfupd E1 E2 P Q :
  AddModal (|NC={E1}=> P) P (|NC={E1,E2}=> Q).
Proof. by rewrite /AddModal ncfupd_frame_r wand_elim_r ncfupd_trans. Qed.

Global Instance elim_acc_ncfupd {X} E1 E2 E α β mγ Q :
  ElimAcc (X:=X) True (ncfupd E1 E2) (ncfupd E2 E1) α β mγ
          (|NC={E1,E}=> Q)
          (λ x, |NC={E2}=> β x ∗ (mγ x -∗? |NC={E1,E}=> Q))%I.
Proof.
  rewrite /ElimAcc.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

Global Instance frame_ncfupd p E1 E2 R P Q :
  Frame p R P Q → Frame p R (|NC={E1,E2}=> P) (|NC={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite ncfupd_frame_l. Qed.

Lemma ncfupd_mask_mono' E1 E2 E1' E2' P : E1 ⊆ E2 → E2' ⊆ E1' → (|NC={E1, E1'}=> P) ⊢ |NC={E2,E2'}=> P.
Proof.
  iIntros (??) "H".
  iMod (ncfupd_mask_subseteq E1) as "Hclo"; auto.
  iMod "H".
  iApply (ncfupd_mask_weaken); auto.
Qed.

(** Introduction lemma for a mask-changing ncfupd.
    This lemma is intended to be [iApply]ed. *)
Lemma ncfupd_mask_intro E1 E2 P :
  E2 ⊆ E1 →
  ((|NC={E2,E1}=> emp) -∗ P) -∗ |NC={E1,E2}=> P.
Proof.
  iIntros (?) "HP". iMod ncfupd_mask_subseteq as "Hclose"; last iModIntro; first done.
  by iApply "HP".
Qed.

Lemma step_ncfupd_mask_mono Eo1 Eo2 Ei1 Ei2 P :
  Ei2 ⊆ Ei1 → Eo1 ⊆ Eo2 →
  (|NC={Eo1,Ei1}=> ▷ |NC={Ei1, Eo1}=> P) ⊢ (|NC={Eo2,Ei2}=> ▷ |NC={Ei2, Eo2}=> P).
Proof.
  intros ??. rewrite -(emp_sep (|NC={Eo1,Ei1}=> ▷ _))%I.
  rewrite (ncfupd_intro_mask Eo2 Eo1 emp%I) //.
  rewrite ncfupd_frame_r -(ncfupd_trans Eo2 Eo1 Ei2). f_equiv.
  rewrite ncfupd_frame_l -(ncfupd_trans Eo1 Ei1 Ei2). f_equiv.
  rewrite (ncfupd_intro_mask Ei1 Ei2 (|NC={_,_}=> emp)%I) //.
  rewrite ncfupd_frame_r. f_equiv.
  rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
  rewrite ncfupd_frame_r -(ncfupd_trans Ei2 Ei1 Eo2). f_equiv.
  rewrite ncfupd_frame_l -(ncfupd_trans Ei1 Eo1 Eo2). f_equiv.
  by rewrite ncfupd_frame_r left_id.
Qed.

Lemma step_ncfupd_intro Ei Eo P : Ei ⊆ Eo → ▷ P -∗ |NC={Eo,Ei}=> ▷ |NC={Ei,Eo}=> P.
Proof. intros. by rewrite -(step_ncfupd_mask_mono Ei _ Ei _) // -!ncfupd_intro. Qed.

Lemma step_ncfupd_wand Eo Ei P Q : (|NC={Eo}[Ei]▷=> P) -∗ (P -∗ Q) -∗ |NC={Eo}[Ei]▷=> Q.
Proof.
  apply wand_intro_l.
  rewrite (later_intro (P -∗ Q)%I).
  iIntros "(HPQ&H)" (q) "HNC".
  iMod ("H" with "[$]") as "H". iModIntro. iNext.
  iMod "H" as "(HP&$)". iModIntro. by iApply "HPQ".
Qed.

Lemma step_ncfupd_ncfupd Eo Ei P : (|NC={Eo}[Ei]▷=> P) ⊣⊢ (|NC={Eo}[Ei]▷=> |NC={Eo}=> P).
Proof.
  apply (anti_symm (⊢)).
  - iIntros "H" (q) "HNC". iMod ("H" with "[$]") as "H".
    iModIntro. iNext. iMod "H" as "(H&$)". iModIntro.
    eauto.
  - iIntros "H" (q) "HNC". iMod ("H" with "[$]") as "H".
    iModIntro. iNext. iMod "H" as "(H&HNC)".
    rewrite ncfupd_eq /ncfupd_def.
    by iMod ("H" with "[$]") as "($&$)".
Qed.

Lemma step_ncfupdN_mono Eo Ei n P Q :
  (P ⊢ Q) → (|NC={Eo}[Ei]▷=>^n P) ⊢ (|NC={Eo}[Ei]▷=>^n Q).
Proof.
  intros HPQ. induction n as [|n IH]=> //=.
  iIntros "H". iApply (step_ncfupd_wand with "H"); eauto.
  iApply IH.
Qed.

Lemma step_ncfupdN_wand Eo Ei n P Q :
  (|NC={Eo}[Ei]▷=>^n P) -∗ (P -∗ Q) -∗ (|NC={Eo}[Ei]▷=>^n Q).
Proof.
  apply wand_intro_l. induction n as [|n IH]=> /=.
  { by rewrite wand_elim_l. }
  iIntros "(HPQ&H)".
  iApply (step_ncfupd_wand with "H"); eauto.
  iIntros. iApply IH. by iFrame.
Qed.

Lemma step_ncfupdN_S_ncfupd n E P:
  (|NC={E}[∅]▷=>^(S n) P) ⊣⊢ (|NC={E}[∅]▷=>^(S n) |NC={E}=> P).
Proof.
  apply (anti_symm (⊢)); rewrite !Nat_iter_S_r; apply step_ncfupdN_mono;
    rewrite -step_ncfupd_ncfupd //.
Qed.

Lemma ncfupd_plainly_later E P : (▷ |NC={E}=> ■ P) ⊢ |NC={E}=> ▷ ◇ P.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "Hshift" (q) "HNC".
  iIntros "[Hw HE]".
  iAssert (▷ ◇ ■ P)%I as "#HP".
  { iNext. by iMod ("Hshift" with "[$] [$]") as "(_ & _ & HP & _)". }
  iModIntro. iModIntro. iFrame. iNext. iMod "HP". eauto.
Qed.

Lemma ncfupd_plain_keep_l E P R `{!Plain P} : (R -∗ |NC={E}=> P) ∗ R ⊢ |NC={E}=> P ∗ R.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  iIntros "(H&R)" (q) "HNC".
  rewrite -assoc. iApply fupd_plain_keep_l. iFrame.
  iIntros "(?&?)". by iDestruct ("H" with "[$] [$]") as ">($&?)".
Qed.

Lemma ncfupd_plain_later E P `{!Plain P} : (▷ |NC={E}=> P) ⊢ |NC={E}=> ▷ ◇ P.
Proof. by rewrite {1}(plain P) ncfupd_plainly_later. Qed.

Lemma step_ncfupd_plain Eo Ei P `{!Plain P} : (|NC={Eo}[Ei]▷=> P) -∗ |NC={Eo}=> ▷ ◇ P.
Proof.
  rewrite ncfupd_eq.
  iIntros "Hshift" (q) "HNC".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "[Hw HE]".
  iAssert (▷ ◇ P)%I as "#HP".
  {
    iMod ("Hshift" with "[$] [$]") as ">(Hw & HE & Hshift)".
    iNext. iMod ("Hshift" with "[$]") as "(Hw & HE & $ & _)".
  }
  iFrame "HP".
  iPoseProof (ncfupd_plain_mask Ei Eo True%I) as "H".
  by iFrame.
Qed.

Lemma step_ncfupdN_plain Eo Ei n P `{!Plain P} : (|NC={Eo}[Ei]▷=>^n P) -∗ |NC={Eo}=> ▷^n ◇ P.
Proof.
  induction n as [|n IH].
  - by rewrite -ncfupd_intro -except_0_intro.
  - rewrite Nat_iter_S. setoid_rewrite IH. rewrite -step_ncfupd_ncfupd step_ncfupd_plain.
    apply ncfupd_mono. destruct n as [|n]; simpl.
    * by rewrite except_0_idemp.
    * by rewrite except_0_later.
Qed.

End ncfupd.

Lemma ncfupd_plain_soundness' `{!invPreG Σ, !crashPreG Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invG Σ} `{Hcrash: !crashG Σ}, ⊢ ∀ q, NC q -∗ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc' as (Hinv) "[Hw HE]".
  iMod NC_alloc as (Hc) "HNC".
  iAssert (NC 1 -∗ |={⊤,E2}=> P)%I as "H".
  { iIntros "HNC". iMod fupd_mask_subseteq; last iApply Hfupd; done. }
  iSpecialize ("H" with "[$]").
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("H" with "[$Hw HE]") as "[Hw [HE >H']]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.

Lemma ncfupd_plain_soundness `{!invPreG Σ, !crashPreG Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invG Σ} `{Hcrash: !crashG Σ}, ⊢ |NC={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc' as (Hinv) "[Hw HE]".
  iMod NC_alloc as (Hc) "HNC".
  iAssert (|NC={⊤,E2}=> P)%I as "H".
  { iMod ncfupd_mask_subseteq; last iApply Hfupd. done. }
  rewrite ncfupd_eq /ncfupd_def.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("H" with "[$HNC] [$Hw HE]") as "[Hw [HE >(H'&_)]]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.

Lemma step_ncfupdN_soundness_alt `{!invPreG Σ, !crashPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ} `{Hcrash: !crashG Σ}, ⊢@{iPropI Σ} ∀ q, NC q -∗ |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (ncfupd_plain_soundness' ⊤ ∅ _)=> Hinv Hcrash.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iIntros (q) "HNC". iSpecialize ("H" with "[$]").
  iMod (step_fupdN_plain with "H") as "H". iMod "H". iModIntro.
  rewrite -later_laterN laterN_later.
  iNext.
  iMod "H" as %Hφ. auto.
Qed.

Lemma step_ncfupdN_soundness `{!invPreG Σ, !crashPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ} `{Hcrash: !crashG Σ}, ⊢@{iPropI Σ} |NC={⊤}[∅]▷=>^n |NC={⊤,∅}=> ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (ncfupd_plain_soundness ⊤ ⊤ _)=> Hinv Hcrash.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  destruct n as [|n].
  - iApply ncfupd_plainly_mask_empty. iMod "H" as %?; auto.
  - iDestruct (step_ncfupdN_wand _ _ _ _ (|NC={⊤}=> ⌜φ⌝)%I with "H []") as "H'".
    { by iApply ncfupd_plain_mask_empty. }
    rewrite -step_ncfupdN_S_ncfupd.
    iMod (step_ncfupdN_plain with "H'") as "Hφ". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "Hφ".
Qed.

Lemma step_ncfupdN_soundness' `{!invPreG Σ, !crashPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ} `{Hcrash: !crashG Σ}, ⊢@{iPropI Σ} |NC={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_ncfupdN_soundness _ n).
  iIntros (Hinv Hcrash). iPoseProof (Hiter Hinv Hcrash) as "Hiter".
  iApply (step_ncfupdN_wand with "Hiter"). by iApply ncfupd_mask_weaken.
Qed.

Global Hint Extern 1 (environments.envs_entails _ (|NC={_}=> _)) => iModIntro : core.
