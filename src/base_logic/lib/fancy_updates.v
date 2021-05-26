From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import tactics.
From Perennial.base_logic.lib Require Export own.
From Perennial.base_logic.lib Require Import wsat.
From iris.prelude Require Import options.
Export invGS.
Import uPred.

(** * Suffix subsets *)
Fixpoint coPset_suffixes_of_raw (p : positive) (E: coPset_raw) : coPset_raw :=
  match p with
  | 1 => E
  | p~0 => coPNode' false (coPset_suffixes_of_raw p E) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_suffixes_of_raw p E)
  end%positive.
Lemma coPset_suffixes_of_wf p E : coPset_wf E → coPset_wf (coPset_suffixes_of_raw p E).
Proof. induction p; simpl; eauto. Qed.
Definition coPset_suffixes_of (p : positive) (E : coPset) : coPset :=
  coPset_suffixes_of_raw p (`E) ↾ coPset_suffixes_of_wf _ _ (proj2_sig E).
Lemma elem_coPset_suffixes_of p q E : p ∈ coPset_suffixes_of q E ↔ ∃ q', (p = Papp q' q) ∧ q' ∈ E.
Proof.
  unfold elem_of, coPset_elem_of; simpl; split.
  - revert p; induction q; intros [?|?|]; simpl;
      rewrite ?coPset_elem_of_node; naive_solver.
  - by intros [q' (->&Helem)]; induction q; simpl; rewrite ?coPset_elem_of_node.
Qed.
Lemma coPset_suffixes_of_top p :
  coPset_suffixes_of p ⊤ = coPset_suffixes p.
Proof.
  rewrite -leibniz_equiv_iff => x.
  rewrite elem_coPset_suffixes_of elem_coPset_suffixes. naive_solver set_solver.
Qed.

Definition coPset_inl (E: coPset) : coPset := coPset_suffixes_of (positives_flatten (1::nil))%positive E.
Definition coPset_inr (E: coPset) : coPset := coPset_suffixes_of (positives_flatten (2::nil))%positive E.

Lemma coPset_suffixes_of_infinite p E:
  (¬ set_finite E) → (¬ set_finite (coPset_suffixes_of p E)).
Proof.
  rewrite ?coPset_finite_spec; simpl. intros Hsuff.
  induction p; simpl; rewrite ?coPset_finite_node; rewrite ?andb_True //=; naive_solver.
Qed.

Lemma coPset_inl_inr_disj E1 E2 :
  coPset_inl E1 ## coPset_inr E2.
Proof.
  intros q. rewrite ?elem_coPset_suffixes_of.
  intros (q1'&Heq1&Hin1) (q2'&Heq2&Hin2).
  rewrite Heq1 in Heq2.
  apply positives_flatten_suffix_eq in Heq2 => //=.
Qed.

Definition AlwaysEn := coPset_inl ⊤.
Definition MaybeEn1 E := coPset_inr (coPset_inr E).
Definition MaybeEn2 E := coPset_inr (coPset_inl E).

Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn2 _) => apply coPset_inl_inr_disj : core.

Definition uPred_fupd_def `{!invGS Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat_all ∗ ownE (AlwaysEn ∪ MaybeEn1 E1) ==∗ ◇ (wsat_all ∗ ownE (AlwaysEn ∪ MaybeEn1 E2) ∗ P).
Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {Σ _}.
Lemma uPred_fupd_eq `{!invGS Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma coPset_suffixes_of_union p E1 E2 :
  coPset_suffixes_of p (E1 ∪ E2) = coPset_suffixes_of p E1 ∪ coPset_suffixes_of p E2.
Proof.
  rewrite -leibniz_equiv_iff.
  intros x. set_unfold. rewrite ?elem_coPset_suffixes_of. set_unfold. naive_solver.
Qed.

Lemma coPset_suffixes_of_disj p E1 E2 :
  E1 ## E2 ↔ coPset_suffixes_of p E1 ## coPset_suffixes_of p E2.
Proof.
  set_unfold. split => Hin x.
  - rewrite ?elem_coPset_suffixes_of.
    intros (q1'&Heq1&Hin1) (q2'&Heq2&Hin2).
    rewrite Heq1 in Heq2.
    apply Papp_inj in Heq2; naive_solver.
  - intros. apply (Hin (Papp x p)); apply elem_coPset_suffixes_of; eauto.
Qed.

Lemma MaybeEn_union E1 E2 : MaybeEn1 (E1 ∪ E2) = MaybeEn1 E1 ∪ MaybeEn1 E2.
Proof.
  rewrite /MaybeEn1/coPset_inr/coPset_inl ?coPset_suffixes_of_union //. Qed.
Lemma MaybeEn_disj E1 E2 : E1 ## E2 ↔ MaybeEn1 E1 ## MaybeEn1 E2.
Proof. rewrite /MaybeEn1/coPset_inr/coPset_inl -?coPset_suffixes_of_disj //. Qed.
Lemma MaybeEn_infinite E:
  (¬ set_finite E) → (¬ set_finite (MaybeEn1 E)).
Proof. intros Hnf. by do 2 apply coPset_suffixes_of_infinite. Qed.

Lemma MaybeEn2_union E1 E2 : MaybeEn2 (E1 ∪ E2) = MaybeEn2 E1 ∪ MaybeEn2 E2.
Proof.
  rewrite /MaybeEn2/coPset_inr/coPset_inl ?coPset_suffixes_of_union //. Qed.
Lemma MaybeEn2_disj E1 E2 : E1 ## E2 ↔ MaybeEn2 E1 ## MaybeEn2 E2.
Proof. rewrite /MaybeEn2/coPset_inr/coPset_inl -?coPset_suffixes_of_disj //. Qed.
Lemma MaybeEn2_infinite E:
  (¬ set_finite E) → (¬ set_finite (MaybeEn2 E)).
Proof. intros Hnf. by do 2 apply coPset_suffixes_of_infinite. Qed.

Lemma ownE_op_MaybeEn `{!invGS Σ} E1 E2 :
  E1 ## E2 → ownE (MaybeEn1 (E1 ∪ E2)) ⊣⊢ ownE (MaybeEn1 E1) ∗ ownE (MaybeEn1 E2).
Proof. intros Hdisj. rewrite MaybeEn_union ownE_op //=. by do 2 apply coPset_suffixes_of_disj. Qed.

Lemma ownE_op_MaybeEn2 `{!invGS Σ} E1 E2 :
  E1 ## E2 → ownE (MaybeEn2 (E1 ∪ E2)) ⊣⊢ ownE (MaybeEn2 E1) ∗ ownE (MaybeEn2 E2).
Proof. intros Hdisj. rewrite MaybeEn2_union ownE_op //=. by do 2 apply coPset_suffixes_of_disj. Qed.

Lemma ownE_op_MaybeEn' `{!invGS Σ} E1 E2 :
  ⌜ E1 ## E2 ⌝ ∧ ownE (MaybeEn1 (E1 ∪ E2)) ⊣⊢ ownE (MaybeEn1 E1) ∗ ownE (MaybeEn1 E2).
Proof. rewrite MaybeEn_union MaybeEn_disj ownE_op' //=. Qed.

Lemma ownE_op_MaybeEn2' `{!invGS Σ} E1 E2 :
  ⌜ E1 ## E2 ⌝ ∧ ownE (MaybeEn2 (E1 ∪ E2)) ⊣⊢ ownE (MaybeEn2 E1) ∗ ownE (MaybeEn2 E2).
Proof. rewrite MaybeEn2_union MaybeEn2_disj ownE_op' //=. Qed.

Lemma uPred_fupd_mixin `{!invGS Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_eq. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_eq /uPred_fupd_def ?ownE_op // ?ownE_op_MaybeEn //.
    by iIntros "($ & $ & ($ & HE)) !> !> [$ [$ $]] !> !>" .
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_eq. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_eq /uPred_fupd_def ?ownE_op // ownE_op_MaybeEn //.
    iIntros "Hvs (Hw & HAE & HE1 & HEf)".
    iMod ("Hvs" with "[Hw HAE HE1]") as ">($ & (HAE & HE2) & HP)"; first by iFrame.
    iDestruct (ownE_op_MaybeEn' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". iFrame. by iApply "HP".
  - rewrite uPred_fupd_eq /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance uPred_bi_fupd `{!invGS Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd `{!invGS Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_eq. by iIntros (E P) ">? [$ $] !> !>". Qed.

Global Instance uPred_bi_fupd_plainly `{!invGS Σ} : BiFUpdPlainly (uPredI (iResUR Σ)).
Proof.
  split.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.

Lemma ownE_mono_le_acc `{!invGS Σ} E1 E2:
  E1 ⊆ E2 →
  ownE E2 -∗ ownE E1 ∗ (ownE E1 -∗ ownE E2).
Proof.
  iIntros (?). replace E2 with (E2 ∖ E1 ∪ E1).
  { rewrite ownE_op; last by set_solver. iIntros "(Hrest&$) H". iFrame. }
  { rewrite difference_union_L. set_solver. }
Qed.

Lemma ownE_weaken `{!invGS Σ} E1 E2 : E2 ⊆ E1 → ownE E1 -∗ ownE E2.
Proof.
  iIntros (?) "H". by iDestruct (ownE_mono_le_acc with "H") as "($&_)".
Qed.

Lemma fupd_plain_soundness `{!invGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc' as (Hinv) "[Hw HE]".
  iAssert (|={⊤,E2}=> P)%I as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. iApply Hfupd. }
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("H" with "[$Hw HE]") as "[Hw [HE >H']]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.

Lemma fupd_plain_soundness_strong `{HIPRE: !invGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS Σ} (Heq_pre: inv_inG = HIPRE), ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc'_strong as (Hinv HEQ) "[Hw HE]".
  iAssert (|={⊤,E2}=> P)%I as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. iApply Hfupd. eauto. }
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("H" with "[$Hw HE]") as "[Hw [HE >H']]"; iFrame.
  iApply (ownE_weaken with "HE"). set_solver.
Qed.

Lemma step_fupdN_soundness `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !invGS Σ}, ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness ⊤ ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask_empty. iMod "H".
  iMod (step_fupdN_plain with "H") as "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as %Hφ. auto.
Qed.

Lemma step_fupdN_soundness_strong `{HIPRE: !invGpreS Σ} φ n :
  (∀ `{Hinv: !invGS Σ} (Heq_pre: inv_inG = HIPRE), ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness_strong ⊤ ⊤ _)=> Hinv Heq.
  iPoseProof (Hiter Hinv) as "H"; first done. clear Hiter.
  iApply fupd_plainly_mask_empty. iMod "H".
  iMod (step_fupdN_plain with "H") as "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as %Hφ. auto.
Qed.

Lemma step_fupdN_soundness' `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !invGS Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness _ n)=>Hinv. destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod Hiter as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.
