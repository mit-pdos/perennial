From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Export fancy_updates crash_token.
From Perennial.base_logic.lib Require Import wsat.
From iris.prelude Require Import options.
Import uPred.

Definition ncfupd_def `{!invGS Σ, !crashGS Σ} (E1 E2 : coPset) (P: iProp Σ) : iProp Σ :=
  ∀ q, NC q -∗ |={E1, E2}=> P ∗ NC q.
Definition ncfupd_aux `{!invGS Σ, !crashGS Σ} : seal (ncfupd_def). Proof. by eexists. Qed.
Definition ncfupd `{!invGS Σ, !crashGS Σ} := ncfupd_aux.(unseal).
Definition ncfupd_eq `{!invGS Σ, !crashGS Σ} : ncfupd = ncfupd_def := ncfupd_aux.(seal_eq).

Arguments ncfupd {Σ I C} : rename.

Notation "|NC={ E1 }=> Q" := (ncfupd E1 E1 Q)
  (at level 99, E1 at level 50, Q at level 200,
   format "'[  ' |NC={ E1 }=>  '/' Q ']'") : bi_scope.
Notation "|@NC={ C , E1 }=> Q" := (ncfupd (C:=C) E1 E1 Q)
  (at level 99, C, E1 at level 50, Q at level 200, only parsing) : bi_scope.
Notation "|NC={ E1 , E2 }=> P" := (ncfupd E1 E2 P)
      (at level 99, E1, E2 at level 50, P at level 200,
       format "'[  ' |NC={ E1 , E2 }=>  '/' P ']'") : bi_scope.
Notation "|@NC={ C , E1 , E2 }=> P" := (ncfupd (C:=C) E1 E2 P)
      (at level 99, C, E1, E2 at level 50, P at level 200, only parsing) : bi_scope.

Notation "|NC={ Eo } [ Ei ]▷=> Q" := (∀ q, NC q -∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> Q ∗ NC q)%I
  (at level 99, Eo, Ei at level 50, Q at level 200,
   format "'[  ' |NC={ Eo } [ Ei ]▷=>  '/' Q ']'") : bi_scope.
Notation "|NC={ E1 } [ E2 ]▷=>^ n Q" := (Nat.iter n (λ P, |NC={E1}[E2]▷=> P) Q)%I
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
   format "'[  ' |NC={ E1 } [ E2 ]▷=>^ n  '/' Q ']'").

Section ncfupd.
Context `{!invGS Σ, !crashGS Σ}.
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
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|NC={E}=> Q).
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

Lemma ncfupd_elim E1 E2 E3 P Q :
  (Q -∗ (|NC={E2,E3}=> P)) → (|NC={E1,E2}=> Q) -∗ (|NC={E1,E3}=> P).
Proof. intros ->. rewrite ncfupd_trans //. Qed.

Global Instance except_0_ncfupd' E1 E2 P :
  IsExcept0 (|NC={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_ncfupd. Qed.

Global Instance from_modal_ncfupd E P :
  FromModal True modality_id (|NC={E}=> P) (|NC={E}=> P) P.
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

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_ncfupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_ncfupd_add_later E1 E2 P :
  £1 -∗ (▷ |NC={E1, E2}=> P) -∗ |NC={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd".
  iMod (lc_fupd_elim_later with "Hf Hupd"). done.
Qed.

End ncfupd.

Lemma nc_fupd_soundness `{!invGpreS Σ, !crashGpreS Σ} n E1 E2 (φ : Prop) :
  (∀ `{Hinv: !invGS Σ} `{Hcrash: !crashGS Σ}, £ n ⊢ ∀ q, NC q -∗ |={E1,E2}=> ⌜φ⌝) → φ.
Proof.
  iIntros (Hfupd). eapply (fupd_soundness n).
  iIntros (?) "Hlc".
  iMod NC_alloc as (Hc) "HNC".
  iApply (Hfupd with "Hlc"). done.
Qed.

Lemma ncfupd_soundness `{!invGpreS Σ, !crashGpreS Σ} n E1 E2 (φ : Prop) :
  (∀ `{Hinv: !invGS Σ} `{Hcrash: !crashGS Σ}, £ n ⊢ |NC={E1,E2}=> ⌜φ⌝) → φ.
Proof.
  iIntros (Hfupd). eapply (fupd_soundness n).
  iIntros (?) "Hlc".
  iMod NC_alloc as (Hc) "HNC".
  iPoseProof (Hfupd with "Hlc") as "Hfupd".
  rewrite ncfupd_eq /ncfupd_def.
  iMod ("Hfupd" with "HNC") as "[? _]". done.
Qed.

Global Hint Extern 1 (environments.envs_entails _ (|NC={_}=> _)) => iModIntro : core.
