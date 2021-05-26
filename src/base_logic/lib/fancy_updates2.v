From stdpp Require Export coPset.
From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Export own.
From Perennial.base_logic.lib Require Import wsat fancy_updates.
From iris.prelude Require Import options.
Export invGS.
Import uPred.

Definition uPred_fupd2_def `{!invGS Σ} (E1a E1b : coPset) (E2a E2b : coPset) (P : iProp Σ) : iProp Σ :=
  wsat_all ∗ ownE (AlwaysEn ∪ MaybeEn1 E1a ∪ MaybeEn2 E1b) ==∗
           ◇ (wsat_all ∗ ownE (AlwaysEn ∪ MaybeEn1 E2a ∪ MaybeEn2 E2b) ∗ P).
Definition uPred_fupd2_aux : seal (@uPred_fupd2_def). Proof. by eexists. Qed.
Definition uPred_fupd2 := uPred_fupd2_aux.(unseal).
Global Arguments uPred_fupd2 {Σ _}.
Lemma uPred_fupd2_eq `{!invGS Σ} : uPred_fupd2 = uPred_fupd2_def.
Proof. rewrite -uPred_fupd2_aux.(seal_eq) //. Qed.

Reserved Notation "||={ E1 | E2 }=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "||={ E1 | E2 }=>  Q").
Reserved Notation "||={ E1a | E1b , E2a | E2b }=> Q"
  (at level 99, E1a, E1b, E2a, E2b, Q at level 200,
   format "||={ E1a | E1b , E2a | E2b }=>  Q").

Notation "||={ E1a | E1b , E2a | E2b }=> Q" := (uPred_fupd2 E1a E1b E2a E2b Q) : bi_scope.
Notation "||={ E1a | E1b }=> Q" := (uPred_fupd2 E1a E1b E1a E1b Q) : bi_scope.

Section fupd2.
Context `{!invGS Σ}.
Implicit Types P: iProp Σ.
Implicit Types E : coPset.

Global Instance fupd2_ne E1a E1b E2a E2b : NonExpansive (uPred_fupd2 E1a E1b E2a E2b).
Proof. rewrite uPred_fupd2_eq. solve_proper. Qed.

Lemma MaybeEn12_disj Ea Eb : MaybeEn1 Ea ## MaybeEn2 Eb.
Proof.
  rewrite /MaybeEn1/MaybeEn2/coPset_inr/coPset_inl.
  apply coPset_suffixes_of_disj.
  symmetry. apply coPset_inl_inr_disj.
Qed.

Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn2 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (MaybeEn1 _ ## MaybeEn2 _) => apply MaybeEn12_disj : core.

Lemma fupd2_intro_mask E1a E1b E2a E2b P :
  E2a ⊆ E1a → E2b ⊆ E1b → P ⊢ ||={E1a | E1b , E2a | E2b}=> ||={E2a | E2b,E1a | E1b}=> P.
Proof.
  intros (E1a''&->&?)%subseteq_disjoint_union_L.
  intros (E1b''&->&?)%subseteq_disjoint_union_L.
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  rewrite ownE_op; last first.
  { apply disjoint_union_l; split; auto. }
  rewrite ownE_op; last first.
  { apply coPset_inl_inr_disj. }
  rewrite ownE_op; last first.
  { apply disjoint_union_l; split; auto. }
  rewrite ownE_op; last first.
  { apply coPset_inl_inr_disj. }
  rewrite ownE_op_MaybeEn //.
  rewrite ownE_op_MaybeEn2 //.
  iIntros "$ ($ & ($ & ($ & HEa)) & $ & HEb) !> !> ($&($&$)&$) !> !>".
  iFrame.
Qed.

Lemma fupd2_mask_intro_subseteq E1a E1b E2a E2b P :
  E2a ⊆ E1a → E2b ⊆ E1b → P ⊢ ||={E1a | E1b , E2a | E2b}=> ||={E2a | E2b,E1a | E1b}=> P.
Proof. apply fupd2_intro_mask. Qed.

Lemma except_0_fupd2 E1a E1b E2a E2b P : ◇ (||={E1a | E1b ,E2a | E2b}=> P) ⊢ ||={E1a | E1b,E2a | E2b}=> P.
Proof.
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  iIntros ">H [Hw HE]". iApply "H"; by iFrame.
Qed.

Lemma fupd2_mono E1a E1b E2a E2b P Q : (P ⊢ Q) → (||={E1a | E1b,E2a | E2b}=> P) ⊢ ||={E1a | E1b,E2a | E2b}=> Q.
Proof.
  rewrite uPred_fupd2_eq. iIntros (HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
Qed.

(* Might need to include empty in defin of fancy_updates *)
(*
Lemma fupd2_fupd E1 E2 P : (||={E1 | ∅,E2 | ∅}=> P) ⊢ |={E1,E2}=> P.
Proof.
  rewrite ?uPred_fupd2_eq ?uPred_fupd_eq /uPred_fupd2_def/uPred_fupd_def.
  rewrite /MaybeEn2.
  rewrite /coPset_inr/coPset_inl.
Abort.
*)

Lemma fupd_fupd2 E1a E2a Eb P : (|={E1a,E2a}=> P) ⊢ ||={E1a | Eb,E2a | Eb}=> P.
Proof.
  rewrite ?uPred_fupd2_eq ?uPred_fupd_eq /uPred_fupd2_def/uPred_fupd_def.
  rewrite ownE_op; last auto.
  rewrite ownE_op; last auto.
  rewrite ownE_op; last first.
  { apply disjoint_union_l; split; auto. }
  rewrite ownE_op; last auto.
  rewrite ownE_op; last first.
  { apply disjoint_union_l; split; auto. }
  rewrite ownE_op; last auto.
  iIntros "H (Hw&((Hae&He1)&He2))".
  iMod ("H" with "[$]") as ">($&($&$))".
  eauto.
Qed.

Lemma fupd2_trans E1a E1b E2a E2b E3a E3b P :
  (||={E1a | E1b,E2a | E2b}=> ||={E2a | E2b,E3a | E3b}=> P) ⊢ ||={E1a | E1b,E3a | E3b}=> P.
Proof.
  rewrite uPred_fupd2_eq. iIntros "HP HwE".
  iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.

Lemma fupd2_mask_frame_r' E1a E1b E2a E2b Efa Efb P:
  E1a ## Efa → E1b ## Efb →
  (||={E1a | E1b,E2a | E2b}=> ⌜E2a ## Efa ∧ E2b ## Efb⌝ → P) ⊢
   ||={E1a ∪ Efa | E1b ∪ Efb,E2a ∪ Efa | E2b ∪ Efb}=> P.
Proof.
  intros HE1Efa HE1Efb.
  rewrite uPred_fupd2_eq /uPred_fupd2_def ?ownE_op //;
          try (apply disjoint_union_l; split; auto).
  rewrite ownE_op_MaybeEn // ownE_op_MaybeEn2 //.
  iIntros "Hvs (Hw & (HAE & (HE1a & HEfa)) & HE1b & HEfb)".
  iMod ("Hvs" with "[Hw HAE HE1a HE1b]") as ">($ & ((HAE & HE2a) & HE2b) & HP)"; first by iFrame.
  iDestruct (ownE_op_MaybeEn' with "[HE2a HEfa]") as "[? $]"; first by iFrame.
  iDestruct (ownE_op_MaybeEn2' with "[HE2b HEfb]") as "[? $]"; first by iFrame.
  iIntros "!> !>". iFrame. iApply "HP"; iSplit; eauto.
Qed.

Lemma fupd2_frame_r E1a E1b E2a E2b P R:
  (||={E1a | E1b,E2a | E2b}=> P) ∗ R ⊢ ||={E1a | E1b,E2a | E2b}=> P ∗ R.
Proof. rewrite uPred_fupd2_eq /uPred_fupd2_def. by iIntros "[HwP $]". Qed.

Global Instance fupd2_proper E1a E1b E2a E2b :
  Proper ((≡) ==> (≡)) (uPred_fupd2 E1a E1b E2a E2b) := ne_proper _.

Global Instance fupd2_mono' E1a E1b E2a E2b : Proper ((⊢) ==> (⊢)) (uPred_fupd2 E1a E1b E2a E2b).
Proof. intros P Q; apply fupd2_mono. Qed.
Global Instance fupd2_flip_mono' E1a E1b E2a E2b :
  Proper (flip (⊢) ==> flip (⊢)) (uPred_fupd2 E1a E1b E2a E2b).
Proof. intros P Q; apply fupd2_mono. Qed.

Lemma bupd_fupd2 Ea Eb P:
  (|==> P) ⊢ ||={Ea | Eb, Ea | Eb}=> P.
Proof. rewrite uPred_fupd2_eq. by iIntros ">? [$ $] !> !>". Qed.

Lemma fupd2_intro Ea Eb P : P ⊢ ||={Ea | Eb, Ea | Eb}=> P.
Proof. by rewrite {1}(fupd2_mask_intro_subseteq Ea Eb Ea Eb P) // fupd2_trans. Qed.
Lemma fupd2_mask_subseteq {E1a E1b} E2a E2b :
  E2a ⊆ E1a → E2b ⊆ E1b → ⊢@{iPropI Σ} ||={E1a | E1b,E2a | E2b}=> ||={E2a | E2b,E1a | E1b}=> emp.
Proof. exact: fupd2_mask_intro_subseteq. Qed.
Lemma fupd2_except_0 E1a E1b E2a E2b P : (||={E1a | E1b,E2a | E2b}=> ◇ P) ⊢ ||={E1a | E1b,E2a | E2b}=> P.
Proof. by rewrite {1}(fupd2_intro E2a E2b P) except_0_fupd2 fupd2_trans. Qed.

Global Instance from_assumption_fupd_level E1a E1b p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (||={E1a | E1b, E1a | E1b}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd2. Qed.

Global Instance from_pure_fupd2 a Ea Eb P φ :
  FromPure a P φ → FromPure a (||={Ea|Eb, Ea|Eb}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd2_intro. Qed.

Lemma fupd2_frame_l E1a E1b E2a E2b R Q : (R ∗ ||={E1a | E1b,E2a | E2b}=> Q) ⊢ ||={E1a | E1b,E2a | E2b}=> R ∗ Q.
Proof. rewrite !(comm _ R); apply fupd2_frame_r. Qed.
Lemma fupd2_wand_l E1a E1b E2a E2b P Q : (P -∗ Q) ∗ (||={E1a|E1b,E2a|E2b}=> P) ⊢ ||={E1a|E1b,E2a|E2b}=> Q.
Proof. by rewrite fupd2_frame_l wand_elim_l. Qed.
Lemma fupd2_wand_r E1a E1b E2a E2b P Q : (||={E1a|E1b,E2a|E2b}=> P) ∗ (P -∗ Q) ⊢ ||={E1a|E1b,E2a|E2b}=> Q.
Proof. by rewrite fupd2_frame_r wand_elim_r. Qed.

Lemma fupd2_mask_intro_discard E1a E1b E2a E2b P : E2a ⊆ E1a → E2b ⊆ E1b → P ⊢ ||={E1a|E1b,E2a|E2b}=> P.
Proof.
  intros ??. rewrite -{1}(right_id emp%I bi_sep P%I).
  rewrite (fupd2_mask_intro_subseteq E1a E1b E2a E2b emp%I) //.
  by rewrite fupd2_frame_l sep_elim_l.
Qed.

Lemma fupd2_mask_frame_r E1a E1b E2a E2b Efa Efb P :
  E1a ## Efa → E1b ## Efb → (||={E1a|E1b,E2a|E2b}=> P) ⊢ ||={E1a ∪ Efa|E1b ∪ Efb,E2a ∪ Efa|E2b ∪ Efb}=> P.
Proof.
  intros ??. rewrite -fupd2_mask_frame_r' //. f_equiv.
  apply impl_intro_l, and_elim_r.
Qed.
Lemma fupd2_mask_mono E1a E1b E2a E2b P :
  E1a ⊆ E2a → E1b ⊆ E2b → (||={E1a|E1b,E1a|E1b}=> P) ⊢ ||={E2a|E2b,E2a|E2b}=> P.
Proof.
  intros (Efa&->&?)%subseteq_disjoint_union_L.
  intros (Efb&->&?)%subseteq_disjoint_union_L.
    by apply fupd2_mask_frame_r.
Qed.

Lemma fupd2_sep E1a E1b P Q :
  (||={E1a|E1b,E1a|E1b}=> P) ∗ (||={E1a|E1b,E1a|E1b}=> Q) ⊢ ||={E1a|E1b,E1a|E1b}=> P ∗ Q.
Proof. by rewrite fupd2_frame_r fupd2_frame_l fupd2_trans. Qed.
Lemma fupd2_mask_frame Ea Eb Ea' Eb' E1a E1b E2a E2b P :
  E1a ⊆ Ea →
  E1b ⊆ Eb →
  (||={E1a|E1b,E2a|E2b}=> ||={E2a ∪ (Ea ∖ E1a)|E2b ∪ (Eb∖ E1b),Ea'|Eb'}=> P) -∗ (||={Ea|Eb,Ea'|Eb'}=> P).
Proof.
  intros ??.
  rewrite (fupd2_mask_frame_r _ _ _ _ (Ea ∖ E1a) (Eb ∖ E1b)); try set_solver.
  rewrite fupd2_trans.
  replace (E1a ∪ Ea ∖ E1a) with Ea by (by apply union_difference_L).
  by replace (E1b ∪ Eb ∖ E1b) with Eb by (by apply union_difference_L).
Qed.

Global Instance into_wand_fupd2 Ea Eb p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (||={Ea|Eb,Ea|Eb}=> R) (||={Ea|Eb,Ea|Eb}=> P) (||={Ea|Eb,Ea|Eb}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd2_sep wand_elim_r.
Qed.

Global Instance into_wand_fupd2_persistent E1a E1b E2a E2b p q R P Q :
  IntoWand false q R P Q → IntoWand p q (||={E1a|E1b,E2a|E2b}=> R) P (||={E1a|E1b,E2a|E2b}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd2_frame_l wand_elim_r.
Qed.

Global Instance into_wand_fupd2_args E1a E1b E2a E2b p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (||={E1a|E1b,E2a|E2b}=> P) (||={E1a|E1b,E2a|E2b}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd2_wand_r.
Qed.

Global Instance from_sep_fupd2 Ea Eb P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (||={Ea|Eb,Ea|Eb}=> P) (||={Ea|Eb,Ea|Eb}=> Q1) (||={Ea|Eb,Ea|Eb}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd2_sep. Qed.

Global Instance from_or_fupd_level E1a E1b E2a E2b P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (||={E1a|E1b,E2a|E2b}=> P) (||={E1a|E1b,E2a|E2b}=> Q1) (||={E1a|E1b,E2a|E2b}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply fupd2_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_exist_fupd2 {A} E1a E1b E2a E2b P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (||={E1a|E1b,E2a|E2b}=> P) (λ a, ||={E1a|E1b,E2a|E2b}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

Global Instance except_0_fupd2' E1a E1b E2a E2b P :
  IsExcept0 (||={E1a|E1b,E2a|E2b}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd2. Qed.

Global Instance from_modal_fupd2 Ea Eb P :
  FromModal True modality_id (||={Ea|Eb, Ea|Eb}=> P) (||={Ea|Eb,Ea|Eb}=> P) P.
Proof. by rewrite /FromModal /= -fupd2_intro. Qed.

Global Instance elim_modal_bupd_fupd2 p E1a E1b E2a E2b P Q :
  ElimModal True p false (|==> P) P (||={E1a|E1b,E2a|E2b}=> Q) (||={E1a|E1b,E2a|E2b}=> Q) | 10.
Proof.
   by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd2 E1a E1b) fupd2_frame_r wand_elim_r fupd2_trans.
Qed.
Global Instance elim_modal_fupd2_fupd2 p E1a E1b E2a E2b E3a E3b P Q :
  ElimModal True p false (||={E1a|E1b,E2a|E2b}=> P) P (||={E1a|E1b,E3a|E3b}=> Q) (||={E2a|E2b,E3a|E3b}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd2_frame_r wand_elim_r fupd2_trans.
Qed.

Global Instance elim_modal_fupd_fupd2 p E1 E2 E3 Eb Eb' P Q :
  ElimModal True p false (|={E1,E2}=> P) P (||={E1|Eb,E3|Eb'}=> Q) (||={E2|Eb,E3|Eb'}=> Q).
Proof.
  rewrite /ElimModal=>?. rewrite (fupd_fupd2) intuitionistically_if_elim /=.
  iIntros "(>H&H2)". iApply ("H2" with "[$]").
Qed.

Global Instance elim_acc_fupd2 {X} E1a E1b E2a E2b Ea Eb α β mγ Q :
  ElimAcc (X:=X) True (uPred_fupd2 E1a E1b E2a E2b) (uPred_fupd2 E2a E2b E1a E1b) α β mγ
          (||={E1a|E1b,Ea|Eb}=> Q)
          (λ x, ||={E2a|E2b,E2a|E2b}=> β x ∗ (mγ x -∗? ||={E1a|E1b,Ea|Eb}=> Q))%I.
Proof.
  rewrite /ElimAcc.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

Global Instance frame_fupd2 p E1a E1b E2a E2b R P Q :
  Frame p R P Q → Frame p R (||={E1a|E1b,E2a|E2b}=> P) (||={E1a|E1b,E2a|E2b}=> Q).
Proof. rewrite /Frame=><-. by rewrite fupd2_frame_l. Qed.

Lemma fupd2_mask_mono' E1a E1b E2a E2b E1a' E1b' E2a' E2b' P :
  E1a ⊆ E2a →
  E1b ⊆ E2b →
  E2a' ⊆ E1a' →
  E2b' ⊆ E1b' →
  (||={E1a|E1b, E1a'|E1b'}=> P) ⊢ ||={E2a|E2b,E2a'|E2b'}=> P.
Proof.
  iIntros (????) "H".
  iMod (fupd2_mask_subseteq E1a E1b) as "Hclo"; auto.
  iMod "H".
  iApply (fupd2_mask_intro_discard); auto.
Qed.

Lemma step_fupd2_mask_mono Eo1a Eo1b Eo2a Eo2b Ei1a Ei1b Ei2a Ei2b P :
  Ei2a ⊆ Ei1a →
  Ei2b ⊆ Ei1b →
  Eo1a ⊆ Eo2a →
  Eo1b ⊆ Eo2b →
  (||={Eo1a|Eo1b,Ei1a|Ei1b}=> ▷ ||={Ei1a|Ei1b, Eo1a|Eo1b}=> P) ⊢ (||={Eo2a|Eo2b,Ei2a|Ei2b}=> ▷ ||={Ei2a|Ei2b, Eo2a|Eo2b}=> P).
Proof.
  intros ????. rewrite -(emp_sep (||={Eo1a|_,Ei1a|_}=> ▷ _))%I.
  rewrite (fupd2_mask_intro_subseteq Eo2a Eo2b Eo1a Eo1b emp%I _ _) //.
  rewrite fupd2_frame_r -(fupd2_trans Eo2a Eo2b Eo1a Eo1b Ei2a Ei2b). f_equiv.
  rewrite fupd2_frame_l -(fupd2_trans Eo1a Eo1b Ei1a Ei1b Ei2a Ei2b). f_equiv.
  rewrite (fupd2_mask_intro_subseteq Ei1a Ei1b Ei2a Ei2b (||={_|_,_|_}=> emp)%I) //.
  rewrite fupd2_frame_r. f_equiv.
  rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
  rewrite fupd2_frame_r -(fupd2_trans Ei2a Ei2b Ei1a Ei1b Eo2a Eo2b). f_equiv.
  rewrite fupd2_frame_l -(fupd2_trans Ei1a Ei1b Eo1a Eo1b Eo2a Eo2b). f_equiv.
  by rewrite fupd2_frame_r left_id.
Qed.

Lemma step_fupd2_intro Eia Eib Eoa Eob P : Eia ⊆ Eoa → Eib ⊆ Eob → ▷ P -∗ ||={Eoa|Eob,Eia|Eib}=> ▷ ||={Eia|Eib,Eoa|Eob}=> P.
Proof.
  intros. rewrite -(step_fupd2_mask_mono Eia Eib _ _ Eia Eib) // -!fupd2_intro //.
Qed.

Lemma fupd2_plainly_mask_empty E1 E2 P :
  (||={E1|E2,∅|∅}=> ■ P) ⊢ ||={E1|E2,E1|E2}=> P.
Proof.
  rewrite uPred_fupd2_eq /uPred_fupd2_def. iIntros "H [Hw HE]".
  iAssert (◇ ■ P)%I as "#>HP".
  { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
  by iFrame.
Qed.

Lemma fupd2_elim E1 E1' E2 E2' E3 E3' P Q :
  (Q -∗ (||={E2|E2',E3|E3'}=> P)) → (||={E1|E1',E2|E2'}=> Q) -∗ (||={E1|E1',E3|E3'}=> P).
Proof. intros ->. rewrite fupd2_trans //. Qed.

Lemma fupd2_plainly_mask E1 E2 E1' E2' P :
  (||={E1|E2,E1'|E2'}=> ■ P) ⊢ ||={E1|E2,E1|E2}=> P.
Proof.
  rewrite -(fupd2_plainly_mask_empty).
  apply fupd2_elim, (fupd2_mask_intro_discard _ _ _); set_solver.
Qed.

Lemma fupd2_plainly_keep_l E1 E2 P R:
  (R -∗ ||={E1|E2,E1|E2}=> ■ P) ∗ R ⊢ ||={E1|E2,E1|E2}=> P ∗ R.
Proof.
  rewrite uPred_fupd2_eq /uPred_fupd2_def. iIntros "[H HQ] [Hw HE]".
  iAssert (◇ ■ P)%I as "#>HP".
  { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
  by iFrame.
Qed.

Lemma fupd2_plainly_later E1 E2 P :
    (▷ ||={E1|E2,E1|E2}=> ■ P) ⊢ ||={E1|E2,E1|E2}=> ▷ ◇ P.
Proof.
  rewrite uPred_fupd2_eq /uPred_fupd2_def. iIntros "H [Hw HE]".
  iAssert (▷ ◇ ■ P)%I as "#HP".
  { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
  iFrame. iIntros "!> !> !>". by iMod "HP".
Qed.

Lemma fupd2_plainly_forall_2 E1 E2 {A} Φ :
    (∀ x : A, ||={E1|E2,E1|E2}=> ■ Φ x) ⊢ ||={E1|E2,E1|E2}=> ∀ x, Φ x.
Proof.
  rewrite uPred_fupd2_eq /uPred_fupd2_def. iIntros "HΦ [Hw HE]".
  iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
  { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
  by iFrame.
Qed.

Lemma fupd2_plain_mask_empty E1 E2 P `{!Plain P} :
  (||={E1|E2,∅|∅}=> P) ⊢ ||={E1|E2,E1|E2}=> P.
Proof. by rewrite {1}(plain P) fupd2_plainly_mask_empty. Qed.

Lemma fupd2_plain_mask E1 E2 E1' E2' P `{!Plain P} :
  (||={E1|E2,E1'|E2'}=> P) ⊢ ||={E1|E2,E1|E2}=> P.
Proof. by rewrite {1}(plain P) fupd2_plainly_mask. Qed.

Lemma fupd2_plain_keep_l E1 E2 P R `{!Plain P}:
  (R -∗ ||={E1|E2,E1|E2}=> P) ∗ R ⊢ ||={E1|E2,E1|E2}=> P ∗ R.
Proof. by rewrite {1}(plain P) fupd2_plainly_keep_l. Qed.

Lemma fupd2_plain_later E1 E2 P `{!Plain P} :
    (▷ ||={E1|E2,E1|E2}=> P) ⊢ ||={E1|E2,E1|E2}=> ▷ ◇ P.
Proof. by rewrite {1}(plain P) fupd2_plainly_later. Qed.

Lemma fupd2_plain_forall_2 E1 E2 {A} Φ `{!∀ x, Plain (Φ x)}:
    (∀ x : A, ||={E1|E2,E1|E2}=> Φ x) ⊢ ||={E1|E2,E1|E2}=> ∀ x, Φ x.
Proof.
  rewrite -fupd2_plainly_forall_2. apply forall_mono=> x.
    by rewrite {1}(plain (Φ _)).
Qed.

Lemma fupd2_forall E1 E1' E2 E2' A (Φ : A → _) :
  (||={E1|E1', E2|E2'}=> ∀ x : A, Φ x) ⊢ ∀ x : A, ||={E1|E1', E2|E2'}=> Φ x.
Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

Lemma fupd2_plainly_elim E1 E2 P : ■ P -∗ ||={E1|E2, E1|E2}=> P.
Proof. by rewrite (fupd2_intro E1 _ (■ P)) fupd2_plainly_mask. Qed.

Lemma fupd2_plain_forall E1 E1' E2 E2' {A} (Φ : A → _) `{!∀ x, Plain (Φ x)} :
  E2 ⊆ E1 →
  E2' ⊆ E1' →
  (||={E1|E1',E2|E2'}=> ∀ x, Φ x) ⊣⊢ (∀ x, ||={E1|E1',E2|E2'}=> Φ x).
Proof.
  intros. apply (anti_symm _); first apply fupd2_forall.
  trans (∀ x, ||={E1|E1', E1|E1'}=> Φ x)%I.
  { apply forall_mono=> x. by rewrite fupd2_plain_mask. }
  rewrite fupd2_plain_forall_2. apply fupd2_elim.
  rewrite {1}(plain (∀ x, Φ x)) (fupd2_mask_intro_discard E1 E1' E2 E2' (■ _)) //.
  apply fupd2_elim. by rewrite fupd2_plainly_elim.
Qed.

Global Instance from_forall_fupd2 (E1 E1' E2 E2' : coPset) (A : Type) P (Φ : A → _) (name : ident_name) :
    TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
    TCOr (TCEq E1' E2') (TCOr (TCEq E1' ⊤) (TCEq E2' ∅)) →
    FromForall P Φ name →
    (∀ x : A, Plain (Φ x)) →
    FromForall (||={E1|E1',E2|E2'}=> P) (λ a : A, (||={E1|E1',E2|E2'}=> Φ a)%I) name.
Proof.
  rewrite /FromForall => -[->|[->|->]] -[->|[->|->]] <- ?; rewrite fupd2_plain_forall; set_solver+.
Qed.

End fupd2.

Lemma fupd2_plain_soundness `{!invGpreS Σ} E1 E1' E2 E2' (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS Σ}, ⊢ ||={E1|E1',E2|E2'}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc' as (Hinv) "[Hw HE]".
  iAssert (||={⊤|⊤,E2|E2'}=> P)%I as "H".
  { iMod (fupd2_mask_subseteq E1 E1') as "_"; [done|done|]. iApply Hfupd. }
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  iMod ("H" with "[$Hw HE]") as "[Hw [HE >H']]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.

Lemma fupd2_plain_soundness_strong `{HIPRE: !invGpreS Σ} E1 E1' E2 E2' (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS Σ} (Heq_pre: inv_inG = HIPRE), ⊢ ||={E1|E1',E2|E2'}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc'_strong as (Hinv HEQ) "[Hw HE]".
  iAssert (||={⊤|⊤,E2|E2'}=> P)%I as "H".
  { iMod (fupd2_mask_subseteq E1 E1') as "_"; [done|done|]. iApply Hfupd. eauto. }
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  iMod ("H" with "[$Hw HE]") as "[Hw [HE >H']]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.
