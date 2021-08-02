From stdpp Require Export coPset.
From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Export own.
From Perennial.base_logic.lib Require Import wsat fancy_updates.
From iris.prelude Require Import options.
Export invGS.
Import uPred.


(* We start by constructing a way to divide up a namespace into a countably infinite sequence of name spaces with *)

Fixpoint ndc (N: namespace) (n: nat) : namespace :=
  match n with
  | O => N
  | S n' => ndc (N.@(1%positive)) n'
  end.

Lemma ndc_tail N n :
  ndc N (S n) = (ndc N n).@(1%positive).
Proof. revert N. induction n => N; first done. rewrite -IHn => //=. Qed.

Definition nomega (N: namespace) (mn: option nat) : coPset :=
  match mn with
  | None => ↑(N.@(2%positive))
  | Some n => ↑(ndc (N.@(1%positive)) n) ∪ ↑(N.@(2%positive))
  end.

Lemma ndc_anti_mono N n1 n2:
  n1 ≤ n2 →
  (↑(ndc N n2) : coPset) ⊆ ↑(ndc N n1).
Proof.
  induction 1.
  - reflexivity.
  - transitivity (↑(ndc N m) : coPset); last auto.
    clear. revert N. induction m => N.
    * rewrite //=. solve_ndisj.
    * rewrite ndc_tail. solve_ndisj.
Qed.

Lemma ndc_subset_root N n:
  (↑ (ndc N n) : coPset) ⊆ ↑N.
Proof.
  induction n; first solve_ndisj. etransitivity; last eauto.
  apply ndc_anti_mono; eauto.
Qed.

Definition ndc_S_diff N n : coPset := (↑ (ndc N n)) ∖ (↑ (ndc N (S n))).

Lemma ndc_compl_S_inf N n: ¬ set_finite (ndc_S_diff N n).
Proof.
  rewrite /ndc_S_diff.
  match goal with
  | [ |- ¬ set_finite ?X ] => cut ((↑ndc N n.@(2%positive)) ⊆ X)
  end.
  { pose proof (nclose_infinite (ndc N n.@(2%positive))) as Hinf. intros => Hfalse.
    apply Hinf. eapply set_finite_subseteq; eauto. }
  rewrite ndc_tail. solve_ndisj.
Qed.

Lemma nomega_anti_mono_Some N n1 n2:
  n1 ≤ n2 →
  nomega N (Some n2) ⊆ nomega N (Some n1).
Proof. intros Hle => //=.  pose proof (ndc_anti_mono (N.@1%positive) n1 n2). set_solver. Qed.

Lemma nomega_anti_mono_None N n:
  nomega N None ⊆ nomega N (Some n).
Proof. rewrite //=. set_solver. Qed.

Definition omega_le (mj1 mj2: option nat) : Prop :=
  match mj1, mj2 with
  | None, _ => True
  | Some n1, Some n2 => n2 ≤ n1
  | _, _ => False
  end.

Lemma omega_le_refl mj : omega_le mj mj.
Proof. destruct mj; simpl; done. Qed.

Lemma nomega_omege_le N mj1 mj2 :
  omega_le mj1 mj2 →
  nomega N mj1 ⊆ nomega N mj2.
Proof.
  destruct mj1, mj2; try (inversion 1; done).
  - apply nomega_anti_mono_Some.
  - intros _. apply nomega_anti_mono_None.
Qed.

Lemma nomega_subset_root N mj :
  nomega N mj ⊆ ↑ N.
Proof.
  destruct mj => //=.
  - apply union_least.
    * etransitivity; first eapply ndc_subset_root. solve_ndisj.
    * solve_ndisj.
  - solve_ndisj.
Qed.

(*
Fixpoint slice_string (j: nat) : namespace :=
  match j with
  | O => nroot
  | S n' => nroot.@(1%positive).@(slice_string n')
  end.
*)

Definition AE'_ns (n : nat) : namespace := nroot.@(1%positive).@(n).
Definition AE' (n: nat) : coPset := ↑(AE'_ns n).
Definition AE'' (n: nat) mj := nomega (AE'_ns n) mj.

Fixpoint AE_full_def (n: nat) :=
  AE' n ∪
  match n with
  | O => ∅
  | S n' => AE_full_def n'
  end.
Definition AE_full_aux : seal AE_full_def. Proof. by eexists. Qed.
Definition AE_full := AE_full_aux.(unseal).
Definition AE_full_eq : AE_full = AE_full_def :=
  AE_full_aux.(seal_eq).

Definition AE_def (n: nat) (mj: option nat) :=
  match n with
  | O => ∅
  | S n' => AE'' n mj ∪ AE_full n'
  end.
Definition AE_aux : seal AE_def. Proof. by eexists. Qed.
Definition AE := AE_aux.(unseal).
Definition AE_eq : AE = AE_def :=
  AE_aux.(seal_eq).

Lemma AlwaysEn_alt : AlwaysEn = ↑(nroot.@(1%positive)).
Proof.
  rewrite /AlwaysEn/coPset_inl ?nclose_eq /nclose_def/up_close.
  rewrite /nroot ndot_eq /ndot_def/encode //=.
  apply coPset_suffixes_of_top.
Qed.

Lemma AE'_disj n1 n2 : n1 ≠ n2 → AE' n1 ## AE' n2.
Proof. solve_ndisj. Qed.
Lemma AE'_disj_AE_full n1 n2 : n1 < n2 → AE' n2 ## AE_full n1.
Proof.
  revert n2. rewrite AE_full_eq.
  induction n1 => n2 Hlt.
  - rewrite //= right_id. apply AE'_disj. lia.
  - rewrite //=.
    feed pose proof (IHn1 n2); first lia.
    feed pose proof (AE'_disj n2 (S n1)); first lia.
    set_solver.
Qed.
Lemma AE_full_mono n1 n2 : n1 ≤ n2 → AE_full n1 ⊆ AE_full n2.
Proof. rewrite AE_full_eq. induction 1; rewrite //=; set_solver. Qed.
Lemma AE'_subset_AlwaysEn n : AE' n ⊆ AlwaysEn.
Proof. rewrite AlwaysEn_alt. solve_ndisj. Qed.
Lemma AE_full_subset_AlwaysEn n : AE_full n ⊆ AlwaysEn.
Proof. rewrite AE_full_eq AlwaysEn_alt. induction n; solve_ndisj. Qed.
Lemma AE_full_MaybeEn_disj n E : AE_full n ## MaybeEn1 E.
Proof.
  pose proof (AE_full_subset_AlwaysEn n).
  cut (AlwaysEn ## MaybeEn1 E); last by apply coPset_inl_inr_disj.
  { set_solver. }
Qed.
Lemma AE''_subset_AE' n mj : AE'' n mj ⊆ AE' n.
Proof. rewrite /AE''/AE'. apply nomega_subset_root. Qed.
Lemma AE''_disj_AE_full n1 n2 mj : n1 < n2 → AE'' n2 mj ## AE_full n1.
Proof.
  pose proof (AE''_subset_AE' n2 mj).
  pose proof (AE'_disj_AE_full n1 n2). intros.
  set_solver.
Qed.
Lemma AE_subset_AE_full n mj : AE n mj ⊆ AE_full n.
Proof.
  rewrite AE_eq AE_full_eq /AE_def /AE_full_def -/AE_full_def.
  destruct n; simpl; try set_solver.
  apply union_least.
  * etransitivity; last eapply union_subseteq_l. apply AE''_subset_AE'.
  * rewrite AE_full_eq; set_solver.
Qed.
Lemma AE_subset_le_AE_full n1 n2 mj : n1 ≤ n2 → AE n1 mj ⊆ AE_full n2.
Proof.
  induction 1.
  - apply AE_subset_AE_full.
  - rewrite AE_full_eq /AE_full_def -/AE_full_def -AE_full_eq.
    set_solver.
Qed.
Lemma AE_full_lt_subset_AE n1 n2 mj : n1 < n2 → AE_full n1 ⊆ AE n2 mj.
Proof.
  induction 1.
  * rewrite AE_eq /AE_def. set_solver.
  * rewrite AE_eq /AE_def. etransitivity; last eapply union_subseteq_r.
    apply AE_full_mono; eauto. lia.
Qed.

Lemma difference_union_same_L (X Y Z : coPset):
  X ## Z → Y ## Z →
  (X ∪ Z) ∖ (Y ∪ Z) = X ∖ Y.
Proof. set_solver. Qed.

Lemma disjoint_subseteq (X Y Z : coPset):
  X ⊆ Y →
  Y ## Z →
  X ## Z.
Proof. set_solver. Qed.

Lemma AE'_disj_lt_AE n1 mj n2 : n1 < n2 → AE n1 mj ## AE' n2.
Proof.
  intros Hlt.
  eapply disjoint_subseteq.
  { eapply AE_subset_AE_full. }
  symmetry. by apply AE'_disj_AE_full.
Qed.

Lemma AE_subset_mono n1 n2 mj1 mj2 :
  (n1 < n2 ∨ (n1 = n2 ∧ omega_le mj1 mj2)) →
  AE n1 mj1 ⊆ AE n2 mj2.
Proof.
  intros [Hlt|Heq].
  - induction Hlt.
    * rewrite AE_eq /= -AE_eq. etransitivity; last eapply union_subseteq_r.
      apply AE_subset_AE_full.
    * transitivity (AE_full m).
      ** apply AE_subset_le_AE_full; lia.
      ** apply AE_full_lt_subset_AE. lia.
  - destruct Heq as (->&Hle).
    rewrite AE_eq /AE_def; destruct n2; first set_solver+.
    rewrite /AE''. apply union_mono_r. by apply nomega_omege_le.
Qed.

Lemma AE_subset_AlwaysEn n mj : AE n mj ⊆ AlwaysEn.
Proof.
  etransitivity; first eapply (AE_subset_le_AE_full n n mj); auto.
  apply AE_full_subset_AlwaysEn.
Qed.

Lemma AE_MaybeEn_disj n mj E : AE n mj ## MaybeEn1 E.
Proof.
  pose proof (AE_full_MaybeEn_disj n E).
  pose proof (AE_subset_AE_full n mj). set_solver.
Qed.

Definition AE_next n mj : coPset :=
  match mj with
  | Some j => AE n (Some (S j))
  | None =>
    match n with
    | O => ∅
    | S n => AE n (Some O)
    end
  end.


Definition AE_S_diff n j : coPset :=
  AE n (Some j) ∖ AE n (Some (S j)).

Definition AE_next_diff n mj : coPset := AE n mj ∖ AE_next n mj.

Lemma AE_S_diff_inf n j: ¬ set_finite (AE_S_diff (S n) j).
Proof.
  rewrite /AE_S_diff.
  rewrite AE_eq /AE_def.
  rewrite difference_union_same_L; swap 1 3.
  { eapply AE''_disj_AE_full; lia. }
  { eapply AE''_disj_AE_full; lia. }
  rewrite /=.
  rewrite difference_union_same_L; swap 1 3.
  { match goal with
      | [ |- ↑ (ndc ?X ?j) ## _] => pose proof (ndc_subset_root X j)
    end. eapply disjoint_subseteq; first eassumption.
    solve_ndisj. }
  { match goal with
      | [ |- ↑ (ndc ?X ?j) ## _] => pose proof (ndc_subset_root X j)
    end. eapply disjoint_subseteq; first eassumption.
    solve_ndisj. }
  apply ndc_compl_S_inf.
Qed.

Lemma AE_next_diff_inf n mj: ¬ set_finite (AE_next_diff (S n) mj).
Proof.
  destruct mj; first apply AE_S_diff_inf.
  rewrite /=. rewrite /AE_next_diff/AE_next. rewrite AE_eq /=.
  match goal with
    | [ |- ¬ set_finite ?X ] => assert (↑ (AE'_ns (S n).@2%positive) ⊆ X)
  end.
  { cut (↑AE'_ns (S n).@2%positive ## AE_def n (Some 0)).
    { set_solver. }
    eapply (disjoint_subseteq _ (AE' (S n))).
    { rewrite /AE'. solve_ndisj. }
    rewrite -AE_eq. symmetry. eapply AE'_disj_lt_AE. lia.
  }
  intros Hfin. eapply set_finite_subseteq in Hfin; last eassumption.
  eapply nclose_infinite; eauto.
Qed.

Local Hint Extern 0 (AE_full _ ## MaybeEn1 _) => apply AE_full_MaybeEn_disj : core.
Local Hint Extern 0 (AE _ _ ## MaybeEn1 _) => apply AE_MaybeEn_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.

Definition uPred_fupd_split_level_def `{!invGS Σ} (E1 E2 : coPset) (k : nat) mj (P : iProp Σ) : iProp Σ :=
  wsat (S k) ∗ ownE (AE (S k) mj ∪ MaybeEn1 E1) ==∗ ◇ (wsat (S k) ∗ ownE (AE (S k) mj ∪ MaybeEn1 E2) ∗ P).
Definition uPred_fupd_split_level_aux `{!invGS Σ} : seal uPred_fupd_split_level_def. Proof. by eexists. Qed.
Definition uPred_fupd_split_level `{!invGS Σ} := uPred_fupd_split_level_aux.(unseal).
Definition uPred_fupd_split_level_eq `{!invGS Σ} : uPred_fupd_split_level = uPred_fupd_split_level_def :=
  uPred_fupd_split_level_aux.(seal_eq).

Definition uPred_fupd_level_def `{!invGS Σ} (E1 E2 : coPset) (k : nat) (P : iProp Σ) : iProp Σ :=
  uPred_fupd_split_level E1 E2 k None P.
Definition uPred_fupd_level_aux `{!invGS Σ} : seal uPred_fupd_level_def. Proof. by eexists. Qed.
Definition uPred_fupd_level `{!invGS Σ} := uPred_fupd_level_aux.(unseal).
Definition uPred_fupd_level_eq `{!invGS Σ} : uPred_fupd_level = uPred_fupd_level_def :=
  uPred_fupd_level_aux.(seal_eq).

Reserved Notation "| k , j ={ E1 }=> Q"
  (at level 99, E1, k at level 50, j at level 50, Q at level 200,
   format "| k , j ={ E1 }=>  Q").
Reserved Notation "| k , j ={ E1 , E2 }=> Q"
  (at level 99, E1, E2, k at level 50, j at level 50, Q at level 200,
   format "| k , j ={ E1 , E2 }=>  Q").
Reserved Notation "| k ={ E1 }=> Q"
  (at level 99, E1, k at level 50, Q at level 200,
   format "| k ={ E1 }=>  Q").
Reserved Notation "| k ={ E1 , E2 }=> Q"
  (at level 99, E1, E2, k at level 50, Q at level 200,
   format "| k ={ E1 , E2 }=>  Q").

(*
Reserved Notation "P = k ={ E1 , E2 }=∗ Q"
  (at level 99, E1,E2, k at level 50, Q at level 200,
   format "'[' P  '/' = k ={ E1 , E2 }=∗  Q ']'").
*)

Notation "| k , j ={ E1 , E2 }=> Q" := (uPred_fupd_split_level E1 E2 k j Q) : bi_scope.
Notation "| k , j ={ E1 }=> Q" := (uPred_fupd_split_level E1 E1 k j Q) : bi_scope.
Notation "| k ={ E1 , E2 }=> Q" := (uPred_fupd_level E1 E2 k Q) : bi_scope.
Notation "| k ={ E1 }=> Q" := (uPred_fupd_level E1 E1 k Q) : bi_scope.
(*
Notation "P = k ={ E1 , E2 }=∗ Q" := (P -∗ |k={E1,E2}=> Q)%I : bi_scope.
Notation "P = k ={ E1 , E2 }=∗ Q" := (P -∗ |k={E1,E2}=> Q) : stdpp_scope.
*)

Section fupd_level.
Context `{!invGS Σ}.
Implicit Types P: iProp Σ.
Implicit Types E : coPset.
Implicit Types j k : nat.
Implicit Types mj : option nat.

Global Instance fupd_split_level_ne E1 E2 k mj : NonExpansive (uPred_fupd_split_level E1 E2 k mj).
Proof. rewrite uPred_fupd_split_level_eq. solve_proper. Qed.
Global Instance fupd_level_ne E1 E2 k : NonExpansive (uPred_fupd_level E1 E2 k).
Proof. rewrite uPred_fupd_level_eq. solve_proper. Qed.

Lemma fupd_split_level_intro_mask E1 E2 k mj P : E2 ⊆ E1 → P ⊢ |k,mj={E1,E2}=> |k,mj={E2,E1}=> P.
Proof.
  intros (E1''&->&?)%subseteq_disjoint_union_L.
  rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def ?ownE_op // ?ownE_op_MaybeEn //.
  by iIntros "$ ($ & $ & $ & HE) !> !> [$ [$ $]] !> !>" .
Qed.

Lemma fupd_level_mask_intro_subseteq E1 E2 k P : E2 ⊆ E1 → P ⊢ |k={E1,E2}=> |k={E2,E1}=> P.
Proof. rewrite uPred_fupd_level_eq; apply fupd_split_level_intro_mask. Qed.

Lemma except_0_fupd_split_level E1 E2 k mj P : ◇ (|k,mj={E1,E2}=> P) ⊢ |k,mj={E1,E2}=> P.
Proof.
  rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
  iIntros ">H [Hw HE]". iApply "H"; by iFrame.
Qed.

Lemma except_0_fupd_level E1 E2 k P : ◇ (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> P.
Proof. rewrite uPred_fupd_level_eq; apply except_0_fupd_split_level. Qed.

Lemma fupd_split_level_mono E1 E2 k mj P Q : (P ⊢ Q) → (|k,mj={E1,E2}=> P) ⊢ |k,mj={E1,E2}=> Q.
Proof.
  rewrite uPred_fupd_split_level_eq. iIntros (HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
Qed.

Lemma fupd_level_mono E1 E2 k P Q : (P ⊢ Q) → (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> Q.
Proof. rewrite uPred_fupd_level_eq; apply fupd_split_level_mono. Qed.

Lemma ownE_AE_split_current_rest k mj :
  ownE (AE (S k) mj) ⊣⊢  ownE (AE_next_diff (S k) mj) ∗ ownE (AE_next (S k) mj).
Proof.
  rewrite /AE_next_diff/AE_next.
  rewrite -ownE_op.
  {
    f_equiv.
    rewrite difference_union_L.
    rewrite (comm_L (∪)) subseteq_union_1_L //.
    destruct mj; apply AE_subset_mono; naive_solver lia.
  }
  set_solver.
Qed.
Lemma ownE_AE_le_acc n1 mj1 n2 mj2 :
  (n1 < n2 ∨ (n1 = n2 ∧ omega_le mj1 mj2)) →
  ownE (AE n2 mj2) -∗ ownE (AE n1 mj1) ∗ (ownE (AE n1 mj1) -∗ ownE (AE n2 mj2)).
Proof. iIntros (?). iApply ownE_mono_le_acc. by apply AE_subset_mono. Qed.

Lemma ownE_AlwaysEn_le_acc n1 mj1 :
  ownE (AlwaysEn) -∗ ownE (AE n1 mj1) ∗ (ownE (AE n1 mj1) -∗ ownE AlwaysEn).
Proof. iApply ownE_mono_le_acc. by apply AE_subset_AlwaysEn. Qed.

Lemma fupd_split_level_le E1 E2 k1 k2 mj1 mj2 P :
  (k1 < k2 ∨ (k1 = k2 ∧ omega_le mj1 mj2)) →
  (|k1,mj1={E1,E2}=> P) ⊢ |k2,mj2={E1,E2}=> P.
Proof.
  rewrite ?uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
  rewrite ?ownE_op //.
  iIntros (Hle) "HP (Hw&HAE&HE)".
  iDestruct (wsat_le_acc (S k1) (S k2) with "Hw") as "(Hw&Hclo)".
  { lia. }
  iDestruct (ownE_AE_le_acc (S k1) mj1 (S k2) mj2 with "HAE") as "(HAE&Hclo')".
  { naive_solver lia. }
  iMod ("HP" with "[$]") as "H". iModIntro.
  iMod "H" as "(Hw&(HAE&HE)&HP)". iFrame.
  iModIntro.
  iDestruct ("Hclo" with "[$]") as "$".
  iDestruct ("Hclo'" with "[$]") as "$".
Qed.

Lemma fupd_level_le E1 E2 k1 k2 P : k1 ≤ k2 → (|k1={E1,E2}=> P) ⊢ |k2={E1,E2}=> P.
Proof. rewrite ?uPred_fupd_level_eq => ?. apply fupd_split_level_le; naive_solver lia. Qed.

Lemma fupd_level_split_level E1 E2 k1 mj k2 P : k1 ≤ k2 → (|k1={E1,E2}=> P) ⊢ |k2,mj={E1,E2}=> P.
Proof. rewrite ?uPred_fupd_level_eq => ?. apply fupd_split_level_le; naive_solver lia. Qed.

Lemma fupd_split_level_fupd E1 E2 P k mj : (|k,mj={E1,E2}=> P) ⊢ |={E1,E2}=> P.
Proof.
  rewrite ?uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
  rewrite ?uPred_fupd_eq /uPred_fupd_def.
  rewrite ?ownE_op //.
  iIntros "HP (Hw&HAE&HE)".
  iMod (wsat_all_acc (S k) with "Hw") as "(Hw&Hclo)".
  iDestruct (ownE_AlwaysEn_le_acc (S k) with "HAE") as "(HAE&Hclo')".
  iMod ("HP" with "[$]") as ">(?&(?&$)&$)".
  do 2 iModIntro.
  iDestruct ("Hclo" with "[$]") as "$".
  iDestruct ("Hclo'" with "[$]") as "$".
Qed.

Lemma fupd_level_fupd E1 E2 P k : (|k={E1,E2}=> P) ⊢ |={E1,E2}=> P.
Proof. rewrite ?uPred_fupd_level_eq. apply fupd_split_level_fupd. Qed.

Lemma fupd_split_level_trans E1 E2 E3 k mj P : (|k,mj={E1,E2}=> |k,mj={E2,E3}=> P) ⊢ |k,mj={E1,E3}=> P.
Proof.
  rewrite uPred_fupd_split_level_eq. iIntros "HP HwE".
  iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.

Lemma fupd_level_trans E1 E2 E3 k P : (|k={E1,E2}=> |k={E2,E3}=> P) ⊢ |k={E1,E3}=> P.
Proof. rewrite uPred_fupd_level_eq; apply fupd_split_level_trans. Qed.

Lemma fupd_split_level_mask_frame_r' E1 E2 Ef k mj P:
    E1 ## Ef → (|k,mj={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |k,mj={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros HE1Ef. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def ?ownE_op // ownE_op_MaybeEn //.
  iIntros "Hvs (Hw & HAE & HE1 & HEf)".
  iMod ("Hvs" with "[Hw HAE HE1]") as ">($ & (HAE & HE2) & HP)"; first by iFrame.
  iDestruct (ownE_op_MaybeEn' with "[HE2 HEf]") as "[? $]"; first by iFrame.
  iIntros "!> !>". iFrame. by iApply "HP".
Qed.

Lemma fupd_level_mask_frame_r' E1 E2 Ef k P:
    E1 ## Ef → (|k={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |k={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof. rewrite uPred_fupd_level_eq; apply fupd_split_level_mask_frame_r'. Qed.

Lemma fupd_split_level_frame_r E1 E2 k mj P R:
  (|k,mj={E1,E2}=> P) ∗ R ⊢ |k,mj={E1,E2}=> P ∗ R.
Proof. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def. by iIntros "[HwP $]". Qed.

Lemma fupd_level_frame_r E1 E2 k P R:
  (|k={E1,E2}=> P) ∗ R ⊢ |k={E1,E2}=> P ∗ R.
Proof. rewrite uPred_fupd_level_eq; apply fupd_split_level_frame_r. Qed.

Global Instance fupd_split_level_proper E1 E2 k mj :
  Proper ((≡) ==> (≡)) (uPred_fupd_split_level E1 E2 k mj) := ne_proper _.
Global Instance fupd_level_proper E1 E2 k :
  Proper ((≡) ==> (≡)) (uPred_fupd_level E1 E2 k) := ne_proper _.


Global Instance fupd_split_mono' E1 E2 k mj : Proper ((⊢) ==> (⊢)) (uPred_fupd_split_level E1 E2 k mj).
Proof. intros P Q; apply fupd_split_level_mono. Qed.
Global Instance fupd_mono' E1 E2 k : Proper ((⊢) ==> (⊢)) (uPred_fupd_level E1 E2 k).
Proof. intros P Q; apply fupd_level_mono. Qed.
Global Instance fupd_split_flip_mono' E1 E2 k mj :
  Proper (flip (⊢) ==> flip (⊢)) (uPred_fupd_split_level E1 E2 k mj).
Proof. intros P Q; apply fupd_split_level_mono. Qed.
Global Instance fupd_flip_mono' E1 E2 k :
  Proper (flip (⊢) ==> flip (⊢)) (uPred_fupd_level E1 E2 k).
Proof. intros P Q; apply fupd_level_mono. Qed.

Lemma bupd_fupd_split_level E k mj P:
  (|==> P) ⊢ |k,mj={E}=> P.
Proof. rewrite uPred_fupd_split_level_eq. by iIntros ">? [$ $] !> !>". Qed.

Lemma bupd_fupd_level E k P:
  (|==> P) ⊢ |k={E}=> P.
Proof. rewrite uPred_fupd_level_eq. apply bupd_fupd_split_level. Qed.

Lemma fupd_level_intro E k P : P ⊢ |k={E}=> P.
Proof. by rewrite {1}(fupd_level_mask_intro_subseteq E E k P) // fupd_level_trans. Qed.
Lemma fupd_level_mask_subseteq {E1} E2 k : E2 ⊆ E1 → ⊢@{iPropI Σ} |k={E1,E2}=> |k={E2,E1}=> emp.
Proof. exact: fupd_level_mask_intro_subseteq. Qed.
Lemma fupd_level_except_0 E1 E2 k P : (|k={E1,E2}=> ◇ P) ⊢ |k={E1,E2}=> P.
Proof. by rewrite {1}(fupd_level_intro E2 k P) except_0_fupd_level fupd_level_trans. Qed.

Global Instance from_assumption_fupd_level E k p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|k={E}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd_level. Qed.

Global Instance from_pure_fupd_level a E k P φ :
  FromPure a P φ → FromPure a (|k={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd_level_intro. Qed.

Lemma fupd_level_frame_l E1 E2 k R Q : (R ∗ |k={E1,E2}=> Q) ⊢ |k={E1,E2}=> R ∗ Q.
Proof. rewrite !(comm _ R); apply fupd_level_frame_r. Qed.
Lemma fupd_level_wand_l E1 E2 k P Q : (P -∗ Q) ∗ (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> Q.
Proof. by rewrite fupd_level_frame_l wand_elim_l. Qed.
Lemma fupd_level_wand_r E1 E2 k P Q : (|k={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |k={E1,E2}=> Q.
Proof. by rewrite fupd_level_frame_r wand_elim_r. Qed.

Lemma fupd_level_mask_intro_discard E1 E2 k P : E2 ⊆ E1 → P ⊢ |k={E1,E2}=> P.
Proof.
  intros ?. rewrite -{1}(right_id emp%I bi_sep P%I).
  rewrite (fupd_level_mask_intro_subseteq E1 E2 k emp%I) //.
  by rewrite fupd_level_frame_l sep_elim_l.
Qed.

Lemma fupd_level_mask_frame_r E1 E2 k Ef P :
  E1 ## Ef → (|k={E1,E2}=> P) ⊢ |k={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros ?. rewrite -fupd_level_mask_frame_r' //. f_equiv.
  apply impl_intro_l, and_elim_r.
Qed.
Lemma fupd_level_mask_mono E1 E2 k P : E1 ⊆ E2 → (|k={E1}=> P) ⊢ |k={E2}=> P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_level_mask_frame_r.
Qed.

Lemma fupd_level_sep E k P Q : (|k={E}=> P) ∗ (|k={E}=> Q) ⊢ |k={E}=> P ∗ Q.
Proof. by rewrite fupd_level_frame_r fupd_level_frame_l fupd_level_trans. Qed.
Lemma fupd_level_mask_frame E E' E1 E2 k P :
  E1 ⊆ E →
  (|k={E1,E2}=> |k={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|k={E,E'}=> P).
Proof.
  intros ?. rewrite (fupd_level_mask_frame_r _ _ _ (E ∖ E1)); last set_solver.
  rewrite fupd_level_trans.
  by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
Qed.

Global Instance into_wand_fupd_level E k p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|k={E}=> R) (|k={E}=> P) (|k={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_level_sep wand_elim_r.
Qed.

Global Instance into_wand_fupd_level_persistent E1 E2 k p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|k={E1,E2}=> R) P (|k={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_level_frame_l wand_elim_r.
Qed.

Global Instance into_wand_fupd_level_args E1 E2 k p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|k={E1,E2}=> P) (|k={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_level_wand_r.
Qed.

Global Instance from_sep_fupd_level E k P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|k={E}=> P) (|k={E}=> Q1) (|k={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_level_sep. Qed.

Global Instance from_or_fupd_level E1 E2 k P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|k={E1,E2}=> P) (|k={E1,E2}=> Q1) (|k={E1,E2}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply fupd_level_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_exist_fupd_level {A} E1 k E2 P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (|k={E1,E2}=> P) (λ a, |k={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

(*
Global Instance from_forall_fupd_level E1 E2 k {A} P (Φ : A → iProp Σ) :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ → (∀ x, Plain (Φ x)) →
  FromForall (|k={E1,E2}=> P)%I (λ a, |k={E1,E2}=> (Φ a))%I.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite fupd_plain_forall; set_solver.
Qed.
*)

Global Instance except_0_fupd_level' E1 E2 k P :
  IsExcept0 (|k={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd_level. Qed.

Global Instance from_modal_fupd_level E k P :
  FromModal True modality_id (|k={E}=> P) (|k={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_level_intro. Qed.

Global Instance elim_modal_bupd_fupd_level p E1 E2 k P Q :
  ElimModal True p false (|==> P) P (|k={E1,E2}=> Q) (|k={E1,E2}=> Q) | 10.
Proof.
   by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd_level E1 k) fupd_level_frame_r wand_elim_r fupd_level_trans.
Qed.
Global Instance elim_modal_fupd_level_fupd_level p E1 E2 E3 k P Q :
  ElimModal True p false (|k={E1,E2}=> P) P (|k={E1,E3}=> Q) (|k={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_level_frame_r wand_elim_r fupd_level_trans.
Qed.
(*
Global Instance elim_modal_fupd_fupd_level p E1 E2 k P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|(S k)={E1,E3}=> Q) (|(S k)={E2,E3}=> Q).
Proof.
  rewrite /ElimModal => ??. rewrite (fupd_fupd_level _ _ k) intuitionistically_if_elim
    fupd_level_frame_r wand_elim_r fupd_level_trans //=.
Qed.
*)

Global Instance elim_acc_fupd_level {X} E1 E2 E k α β mγ Q :
  ElimAcc (X:=X) True (uPred_fupd_level E1 E2 k) (uPred_fupd_level E2 E1 k) α β mγ
          (|k={E1,E}=> Q)
          (λ x, |k={E2}=> β x ∗ (mγ x -∗? |k={E1,E}=> Q))%I.
Proof.
  rewrite /ElimAcc.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

Global Instance frame_fupd_level p E1 E2 k R P Q :
  Frame p R P Q → Frame p R (|k={E1,E2}=> P) (|k={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite fupd_level_frame_l. Qed.

Lemma fupd_level_mask_mono' E1 E2 E1' E2' k P : E1 ⊆ E2 → E2' ⊆ E1' → (|k={E1, E1'}=> P) ⊢ |k={E2,E2'}=> P.
Proof.
  iIntros (??) "H".
  iMod (fupd_level_mask_subseteq E1) as "Hclo"; auto.
  iMod "H".
  iApply (fupd_level_mask_intro_discard); auto.
Qed.

Lemma step_fupd_level_mask_mono Eo1 Eo2 Ei1 Ei2 k P :
  Ei2 ⊆ Ei1 → Eo1 ⊆ Eo2 →
  (|k={Eo1,Ei1}=> ▷ |k={Ei1, Eo1}=> P) ⊢ (|k={Eo2,Ei2}=> ▷ |k={Ei2, Eo2}=> P).
Proof.
  intros ??. rewrite -(emp_sep (|k={Eo1,Ei1}=> ▷ _))%I.
  rewrite (fupd_level_mask_intro_subseteq Eo2 Eo1 _ emp%I) //.
  rewrite fupd_level_frame_r -(fupd_level_trans Eo2 Eo1 Ei2). f_equiv.
  rewrite fupd_level_frame_l -(fupd_level_trans Eo1 Ei1 Ei2). f_equiv.
  rewrite (fupd_level_mask_intro_subseteq Ei1 Ei2 _ (|k={_,_}=> emp)%I) //.
  rewrite fupd_level_frame_r. f_equiv.
  rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
  rewrite fupd_level_frame_r -(fupd_level_trans Ei2 Ei1 Eo2). f_equiv.
  rewrite fupd_level_frame_l -(fupd_level_trans Ei1 Eo1 Eo2). f_equiv.
  by rewrite fupd_level_frame_r left_id.
Qed.

Lemma step_fupd_level_intro Ei Eo k P : Ei ⊆ Eo → ▷ P -∗ |k={Eo,Ei}=> ▷ |k={Ei,Eo}=> P.
Proof. intros. by rewrite -(step_fupd_level_mask_mono Ei _ Ei _) // -!fupd_level_intro. Qed.

End fupd_level.

Section fupd_split_level.
Context `{!invGS Σ}.
Lemma fupd_split_level_intro E k mj P : P ⊢ |k,mj={E}=> P.
Proof. by rewrite {1}(fupd_split_level_intro_mask E E k mj P) // fupd_split_level_trans. Qed.
Lemma fupd_split_level_intro_mask' E1 E2 k mj : E2 ⊆ E1 → ⊢@{iPropI Σ} |k,mj={E1,E2}=> |k,mj={E2,E1}=> emp.
Proof. exact: fupd_split_level_intro_mask. Qed.
Lemma fupd_split_level_except_0 E1 E2 k mj P : (|k,mj={E1,E2}=> ◇ P) ⊢ |k,mj={E1,E2}=> P.
Proof. by rewrite {1}(fupd_split_level_intro E2 k mj P) except_0_fupd_split_level fupd_split_level_trans. Qed.

Global Instance from_assumption_fupd_split_level E k mj p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|k,mj={E}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd_split_level. Qed.

Global Instance from_pure_fupd_split_level a E k mj P φ :
  FromPure a P φ → FromPure a (|k,mj={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd_split_level_intro. Qed.

Lemma fupd_split_level_frame_l E1 E2 k mj R Q : (R ∗ |k,mj={E1,E2}=> Q) ⊢ |k,mj={E1,E2}=> R ∗ Q.
Proof. rewrite !(comm _ R). apply fupd_split_level_frame_r. Qed.
Lemma fupd_split_level_wand_l E1 E2 k mj P Q : (P -∗ Q) ∗ (|k,mj={E1,E2}=> P) ⊢ |k,mj={E1,E2}=> Q.
Proof. by rewrite fupd_split_level_frame_l wand_elim_l. Qed.
Lemma fupd_split_level_wand_r E1 E2 k mj P Q : (|k,mj={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |k,mj={E1,E2}=> Q.
Proof. by rewrite fupd_split_level_frame_r wand_elim_r. Qed.

Lemma fupd_split_level_mask_weaken E1 E2 k mj P : E2 ⊆ E1 → P ⊢ |k,mj={E1,E2}=> P.
Proof.
  intros ?. rewrite -{1}(right_id emp%I bi_sep P%I).
  rewrite (fupd_split_level_intro_mask E1 E2 k mj emp%I) //.
  by rewrite fupd_split_level_frame_l sep_elim_l.
Qed.

Lemma fupd_split_level_mask_frame_r E1 E2 k mj Ef P :
  E1 ## Ef → (|k,mj={E1,E2}=> P) ⊢ |k,mj={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros ?. rewrite -fupd_split_level_mask_frame_r' //. f_equiv.
  apply impl_intro_l, and_elim_r.
Qed.
Lemma fupd_split_level_mask_mono E1 E2 k mj P : E1 ⊆ E2 → (|k,mj={E1}=> P) ⊢ |k,mj={E2}=> P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_split_level_mask_frame_r.
Qed.

Lemma fupd_split_level_sep E k mj P Q : (|k,mj={E}=> P) ∗ (|k,mj={E}=> Q) ⊢ |k,mj={E}=> P ∗ Q.
Proof. by rewrite fupd_split_level_frame_r fupd_split_level_frame_l fupd_split_level_trans. Qed.
Lemma fupd_split_level_mask_frame E E' E1 E2 k mj P :
  E1 ⊆ E →
  (|k,mj={E1,E2}=> |k,mj={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|k,mj={E,E'}=> P).
Proof.
  intros ?. rewrite (fupd_split_level_mask_frame_r _ _ _ _ (E ∖ E1)); last set_solver.
  rewrite fupd_split_level_trans.
  by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
Qed.

Global Instance into_wand_fupd_split_level E k mj p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|k,mj={E}=> R) (|k,mj={E}=> P) (|k,mj={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_split_level_sep wand_elim_r.
Qed.

Global Instance into_wand_fupd_split_level_persistent E1 E2 k mj p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|k,mj={E1,E2}=> R) P (|k,mj={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_split_level_frame_l wand_elim_r.
Qed.

Global Instance into_wand_fupd_split_level_args E1 E2 k mj p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|k,mj={E1,E2}=> P) (|k,mj={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_split_level_wand_r.
Qed.

Global Instance from_sep_fupd_split_level E k mj P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|k,mj={E}=> P) (|k,mj={E}=> Q1) (|k,mj={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_split_level_sep. Qed.

Global Instance from_or_fupd_split_level E1 E2 k mj P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|k,mj={E1,E2}=> P) (|k,mj={E1,E2}=> Q1) (|k,mj={E1,E2}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply fupd_split_level_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_exist_fupd_split_level {A} E1 k mj E2 P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (|k,mj={E1,E2}=> P) (λ a, |k,mj={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

(*
Global Instance from_forall_fupd_split_level E1 E2 k mj {A} P (Φ : A → iProp Σ) :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ → (∀ x, Plain (Φ x)) →
  FromForall (|k,mj={E1,E2}=> P)%I (λ a, |k,mj={E1,E2}=> (Φ a))%I.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite fupd_plain_forall; set_solver.
Qed.
*)

Global Instance except_0_fupd_split_level' E1 E2 k mj P :
  IsExcept0 (|k,mj={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd_split_level. Qed.

Global Instance from_modal_fupd_split_level E k mj P :
  FromModal True modality_id (|k,mj={E}=> P) (|k,mj={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_split_level_intro. Qed.

Global Instance elim_modal_bupd_fupd_split_level p E1 E2 k mj P Q :
  ElimModal True p false (|==> P) P (|k,mj={E1,E2}=> Q) (|k,mj={E1,E2}=> Q) | 10.
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd_split_level E1 k mj) fupd_split_level_frame_r wand_elim_r fupd_split_level_trans.
Qed.
Global Instance elim_modal_fupd_split_level_fupd_split_level p E1 E2 E3 k mj P Q :
  ElimModal True p false (|k,mj={E1,E2}=> P) P (|k,mj={E1,E3}=> Q) (|k,mj={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_split_level_frame_r wand_elim_r fupd_split_level_trans.
Qed.

Global Instance elim_modal_fupd_level_fupd p E1 E2 E3 k P Q :
  ElimModal True p false (|(S k)={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof.
  rewrite /ElimModal=>?. rewrite (fupd_level_fupd) intuitionistically_if_elim /=.
  iIntros "(>H&H2)". iApply ("H2" with "[$]").
Qed.

Global Instance elim_acc_fupd_split_level {X} E1 E2 E k mj α β mγ Q :
  ElimAcc (X:=X) True (uPred_fupd_split_level E1 E2 k mj) (uPred_fupd_split_level E2 E1 k mj) α β mγ
          (|k,mj={E1,E}=> Q)
          (λ x, |k,mj={E2}=> β x ∗ (mγ x -∗? |k,mj={E1,E}=> Q))%I.
Proof.
  rewrite /ElimAcc.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

Global Instance frame_fupd_split_level p E1 E2 k mj R P Q :
  Frame p R P Q → Frame p R (|k,mj={E1,E2}=> P) (|k,mj={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite fupd_split_level_frame_l. Qed.

Lemma fupd_split_level_mask_mono' E1 E2 E1' E2' k mj P : E1 ⊆ E2 → E2' ⊆ E1' → (|k,mj={E1, E1'}=> P) ⊢ |k,mj={E2,E2'}=> P.
Proof.
  iIntros (??) "H".
  iMod (fupd_split_level_intro_mask' _ E1) as "Hclo"; auto.
  iMod "H".
  iApply (fupd_split_level_mask_weaken); auto.
Qed.

End fupd_split_level.

Section schema_test_fupd.
Context `{!invGS Σ}.
Implicit Types P : iProp Σ.

Definition bi_sch_False : bi_schema := bi_sch_pure False.

Definition bi_sch_except_0 (P: bi_schema) : bi_schema :=
  bi_sch_or (bi_sch_later (bi_sch_False)) P.

Definition bi_sch_bupd_wand (P1 P2: bi_schema) :=
  bi_sch_wand P1 (bi_sch_bupd P2).

Definition bi_sch_fupd_mj E1 E2 mj (P: bi_schema) : bi_schema :=
  bi_sch_bupd_wand
    (bi_sch_sep (bi_sch_wsat) (bi_sch_ownE (λ k, AE k mj ∪ MaybeEn1 E1)))
    (bi_sch_except_0 (bi_sch_sep (bi_sch_wsat)
                                (bi_sch_sep (bi_sch_ownE (λ k, AE k mj ∪ MaybeEn1 E2)) P))).

Definition bi_sch_fupd E1 E2 (P: bi_schema) : bi_schema :=
  bi_sch_bupd_wand
    (bi_sch_sep (bi_sch_wsat) (bi_sch_ownE (λ k, AE k (Some O) ∪ MaybeEn1 E1)))
    (bi_sch_except_0 (bi_sch_sep (bi_sch_wsat)
                                (bi_sch_sep (bi_sch_ownE (λ k, AE k (Some O) ∪ MaybeEn1 E2)) P))).

Lemma bi_sch_fupd_interp' E1 E2 lvl Qs Qs_mut Psch P:
  bi_schema_interp lvl Qs Qs_mut Psch = P →
  bi_schema_interp lvl Qs Qs_mut (bi_sch_fupd E1 E2 Psch) =
    (wsat lvl ∗ ownE (AE lvl (Some 0) ∪ MaybeEn1 E1) ==∗ ◇ (wsat lvl ∗ ownE (AE lvl (Some 0) ∪ MaybeEn1 E2) ∗ P))%I.
Proof.
  intros Heq.
  rewrite ?bi_schema_interp_unfold //=.
  do 11 (rewrite {1}bi_schema_interp_unfold //=).
  rewrite Heq. rewrite ?bi_schema_interp_unfold //=.
Qed.

Lemma bi_sch_fupd_interp E1 E2 lvl Qs Qs_mut Psch P:
  bi_schema_interp (S lvl) Qs Qs_mut Psch = P →
  bi_schema_interp (S lvl) Qs Qs_mut (bi_sch_fupd E1 E2 Psch) =
  (|lvl,(Some 0)={E1, E2}=> P)%I.
Proof.
  intros Heq. rewrite uPred_fupd_split_level_eq. by apply bi_sch_fupd_interp'.
Qed.

Lemma bi_sch_fupd_interp_mj' E1 E2 lvl mj Qs Qs_mut Psch P:
  bi_schema_interp lvl Qs Qs_mut Psch = P →
  bi_schema_interp lvl Qs Qs_mut (bi_sch_fupd_mj E1 E2 mj Psch) =
    (wsat lvl ∗ ownE (AE lvl mj ∪ MaybeEn1 E1) ==∗ ◇ (wsat lvl ∗ ownE (AE lvl mj ∪ MaybeEn1 E2) ∗ P))%I.
Proof.
  intros Heq.
  rewrite ?bi_schema_interp_unfold //=.
  do 11 (rewrite {1}bi_schema_interp_unfold //=).
  rewrite Heq. rewrite ?bi_schema_interp_unfold //=.
Qed.

Lemma bi_sch_fupd_interp_mj E1 E2 lvl mj Qs Qs_mut Psch P:
  bi_schema_interp (S lvl) Qs Qs_mut Psch = P →
  bi_schema_interp (S lvl) Qs Qs_mut (bi_sch_fupd_mj E1 E2 mj Psch) =
  (|lvl,mj={E1, E2}=> P)%I.
Proof.
  intros Heq. rewrite uPred_fupd_split_level_eq. by apply bi_sch_fupd_interp_mj'.
Qed.

End schema_test_fupd.
