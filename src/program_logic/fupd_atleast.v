From stdpp Require Export coPset.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat fancy_updates.
From Perennial.algebra Require Import atleast.
Set Default Proof Using "Type".
Export invG.
Import uPred.

(* This is essentially fancy_updates.v from Iris, but replacing the use of except_0 with atleast *)

Definition uPred_fupd_atleast_def `{!invG Σ} (E1 E2 : coPset) (k : nat) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 ==∗ ◇_k (wsat ∗ ownE E2 ∗ P).
Definition uPred_fupd_atleast_aux `{!invG Σ} : seal uPred_fupd_atleast_def. Proof. by eexists. Qed.
Definition uPred_fupd_atleast `{!invG Σ} := uPred_fupd_atleast_aux.(unseal).
Definition uPred_fupd_atleast_eq `{!invG Σ} : uPred_fupd_atleast = uPred_fupd_atleast_def :=
  uPred_fupd_atleast_aux.(seal_eq).

Reserved Notation "| k ={ E1 }=> Q"
  (at level 99, E1, k at level 50, Q at level 200,
   format "| k ={ E1 }=>  Q").
Reserved Notation "| k ={ E1 , E2 }=> Q"
  (at level 99, E1, E2, k at level 50, Q at level 200,
   format "| k ={ E1 , E2 }=>  Q").
Reserved Notation "P = k ={ E1 , E2 }=∗ Q"
  (at level 99, E1,E2, k at level 50, Q at level 200,
   format "'[' P  '/' = k ={ E1 , E2 }=∗  Q ']'").

Notation "| k ={ E1 , E2 }=> Q" := (uPred_fupd_atleast E1 E2 k Q) : bi_scope.
Notation "| k ={ E1 }=> Q" := (uPred_fupd_atleast E1 E1 k Q) : bi_scope.
Notation "P = k ={ E1 , E2 }=∗ Q" := (P -∗ |k={E1,E2}=> Q)%I : bi_scope.
Notation "P = k ={ E1 , E2 }=∗ Q" := (P -∗ |k={E1,E2}=> Q) : stdpp_scope.

Section fupd_atleast.
Context `{!invG Σ}.
Implicit Types P: iProp Σ.
Implicit Types E : coPset.
Implicit Types k : nat.

Global Instance fupd_atleast_ne E1 E2 k: NonExpansive (uPred_fupd_atleast E1 E2 k).
Proof. rewrite uPred_fupd_atleast_eq. solve_proper. Qed.

Lemma fupd_atleast_intro_mask E1 E2 k P : E2 ⊆ E1 → P ⊢ |k={E1,E2}=> |k={E2,E1}=> P.
Proof.
  intros (E1''&->&?)%subseteq_disjoint_union_L.
  rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def ownE_op //.
  by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>" .
Qed.

Lemma atleast_fupd_atleast E1 E2 k P : ◇_k (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> P.
Proof.
  rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def.
  iIntros ">H [Hw HE]". iApply "H"; by iFrame.
Qed.

Lemma fupd_atleast_mono E1 E2 k P Q : (P ⊢ Q) → (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> Q.
Proof.
  rewrite uPred_fupd_atleast_eq. iIntros (HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
Qed.

Lemma fupd_atleast_le E1 E2 k1 k2 P : k1 ≤ k2 → (|k1={E1,E2}=> P) ⊢ |k2={E1,E2}=> P.
Proof.
  rewrite ?uPred_fupd_atleast_eq /uPred_fupd_atleast_def.
  iIntros (Hle) "HP HwE". iMod ("HP" with "[$]"). iModIntro.
  by iApply (atleast_le).
Qed.

Lemma fupd_fupd_atleast1 E1 E2 P : (|={E1,E2}=> P) ⊣⊢ |1={E1,E2}=> P.
Proof.
  rewrite ?uPred_fupd_atleast_eq /uPred_fupd_atleast_def.
  rewrite ?uPred_fupd_eq /uPred_fupd_def.
  by rewrite except_0_atleast.
Qed.

Lemma fupd_fupd_atleast E1 E2 k P : (|={E1,E2}=> P) ⊢ |(S k)={E1,E2}=> P.
Proof.
  rewrite fupd_fupd_atleast1. apply fupd_atleast_le. lia.
Qed.

Lemma fupd_atleast_trans E1 E2 E3 k P : (|k={E1,E2}=> |k={E2,E3}=> P) ⊢ |k={E1,E3}=> P.
Proof.
  rewrite uPred_fupd_atleast_eq. iIntros "HP HwE".
  iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.

Lemma fupd_atleast_mask_frame_r' E1 E2 Ef k P:
    E1 ## Ef → (|k={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |k={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros HE1Ef. rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def ownE_op //.
  iIntros "Hvs (Hw & HE1 &HEf)".
  iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
  iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
  iIntros "!> !>". by iApply "HP".
Qed.

Lemma fupd_atleast_frame_r E1 E2 k P R:
  (|k={E1,E2}=> P) ∗ R ⊢ |k={E1,E2}=> P ∗ R.
Proof.
  rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def. by iIntros "[HwP $]".
Qed.

(*
Instance uPred_bi_fupd_atleast `{!invG Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_atleast_mixin |}.

Instance uPred_bi_bupd_fupd_atleast `{!invG Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFupd_Atleast uPred_fupd_atleast_eq. by iIntros (E P) ">? [$ $] !> !>". Qed.
*)

(*
Instance uPred_bi_fupd_atleast_plainly `{!invG Σ} : BiFUpdPlainly (uPredI (iResUR Σ)).
Proof.
  split.
  - rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def. iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def. iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def. iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def. iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.
*)
Global Instance fupd_atleast_proper E1 E2 k :
  Proper ((≡) ==> (≡)) (uPred_fupd_atleast E1 E2 k) := ne_proper _.

Global Instance fupd_mono' E1 E2 k : Proper ((⊢) ==> (⊢)) (uPred_fupd_atleast E1 E2 k).
Proof. intros P Q; apply fupd_atleast_mono. Qed.
Global Instance fupd_flip_mono' E1 E2 k :
  Proper (flip (⊢) ==> flip (⊢)) (uPred_fupd_atleast E1 E2 k).
Proof. intros P Q; apply fupd_atleast_mono. Qed.

Lemma bupd_fupd_atleast E k P:
  (|==> P) ⊢ |k={E}=> P.
Proof. rewrite uPred_fupd_atleast_eq. by iIntros ">? [$ $] !> !>". Qed.

Lemma fupd_atleast_intro E k P : P ⊢ |k={E}=> P.
Proof. by rewrite {1}(fupd_atleast_intro_mask E E k P) // fupd_atleast_trans. Qed.

Global Instance from_assumption_fupd_atleast E k p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|k={E}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd_atleast. Qed.

Global Instance from_pure_fupd_atleast a E k P φ :
  FromPure a P φ → FromPure a (|k={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd_atleast_intro. Qed.

Lemma fupd_atleast_frame_l E1 E2 k R Q : (R ∗ |k={E1,E2}=> Q) ⊢ |k={E1,E2}=> R ∗ Q.
Proof. rewrite !(comm _ R); apply fupd_atleast_frame_r. Qed.
Lemma fupd_atleast_wand_l E1 E2 k P Q : (P -∗ Q) ∗ (|k={E1,E2}=> P) ⊢ |k={E1,E2}=> Q.
Proof. by rewrite fupd_atleast_frame_l wand_elim_l. Qed.
Lemma fupd_atleast_wand_r E1 E2 k P Q : (|k={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |k={E1,E2}=> Q.
Proof. by rewrite fupd_atleast_frame_r wand_elim_r. Qed.

Lemma fupd_atleast_sep E k P Q : (|k={E}=> P) ∗ (|k={E}=> Q) ⊢ |k={E}=> P ∗ Q.
Proof. by rewrite fupd_atleast_frame_r fupd_atleast_frame_l fupd_atleast_trans. Qed.

Global Instance into_wand_fupd_atleast E k p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|k={E}=> R) (|k={E}=> P) (|k={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_atleast_sep wand_elim_r.
Qed.

Global Instance into_wand_fupd_atleast_persistent E1 E2 k p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|k={E1,E2}=> R) P (|k={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_atleast_frame_l wand_elim_r.
Qed.

Global Instance into_wand_fupd_atleast_args E1 E2 k p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|k={E1,E2}=> P) (|k={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_atleast_wand_r.
Qed.

Global Instance from_sep_fupd_atleast E k P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|k={E}=> P) (|k={E}=> Q1) (|k={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_atleast_sep. Qed.

Global Instance from_or_fupd_atleast E1 E2 k P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|k={E1,E2}=> P) (|k={E1,E2}=> Q1) (|k={E1,E2}=> Q2).
  rewrite /FromOr=><-. apply or_elim; apply fupd_atleast_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_exist_fupd_atleast {A} E1 k E2 P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (|k={E1,E2}=> P) (λ a, |k={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

(*
Global Instance from_forall_fupd_atleast E1 E2 k {A} P (Φ : A → iProp Σ) :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ → (∀ x, Plain (Φ x)) →
  FromForall (|k={E1,E2}=> P)%I (λ a, |k={E1,E2}=> (Φ a))%I.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite fupd_plain_forall; set_solver.
Qed.
*)

Global Instance is_atleast_fupd_atleast E1 E2 k P :
  IsAtLeast k (|k={E1,E2}=> P).
Proof. by rewrite /IsAtLeast atleast_fupd_atleast. Qed.

Global Instance from_modal_fupd_atleast E k P :
  FromModal modality_id (|k={E}=> P) (|k={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_atleast_intro. Qed.

Global Instance elim_modal_bupd_fupd_atleast p E1 E2 k P Q :
  ElimModal True p false (|==> P) P (|k={E1,E2}=> Q) (|k={E1,E2}=> Q) | 10.
Proof.
   by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd_atleast E1 k) fupd_atleast_frame_r wand_elim_r fupd_atleast_trans.
Qed.
Global Instance elim_modal_fupd_atleast_fupd_atleast p E1 E2 E3 k P Q :
  ElimModal True p false (|k={E1,E2}=> P) P (|k={E1,E3}=> Q) (|k={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_atleast_frame_r wand_elim_r fupd_atleast_trans.
Qed.
Global Instance elim_modal_fupd_fupd_atleast p E1 E2 k P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|(S k)={E1,E3}=> Q) (|(S k)={E2,E3}=> Q).
Proof.
  rewrite /ElimModal => ??. rewrite (fupd_fupd_atleast _ _ k) intuitionistically_if_elim
    fupd_atleast_frame_r wand_elim_r fupd_atleast_trans //=.
Qed.

Global Instance elim_acc_fupd_atleast {X} E1 E2 E k α β mγ Q :
  ElimAcc (X:=X) (uPred_fupd_atleast E1 E2 k) (uPred_fupd_atleast E2 E1 k) α β mγ
          (|k={E1,E}=> Q)
          (λ x, |k={E2}=> β x ∗ (mγ x -∗? |k={E1,E}=> Q))%I.
Proof.
  rewrite /ElimAcc.
  iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

Lemma fupd_atleast_intro_mask' k E1 E2 : E2 ⊆ E1 → ⊢ |k={E1,E2}=> |k={E2,E1}=> emp.
Proof. apply fupd_atleast_intro_mask. Qed.
End fupd_atleast.

Section fupd_atleast.
Context `{!invG Σ}.
Implicit Types P: iProp Σ.
Implicit Types E : coPset.
Implicit Types k : nat.

Lemma fupd_atleast_plain_soundness `{!invPreG Σ} E1 E2 k (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invG Σ}, ⊢ |k={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd_atleast). apply (laterN_soundness _ k); simpl.
   iMod wsat_alloc as (Hinv) "[Hw HE]".
  iAssert (|k={⊤,E2}=> P)%I as "H".
  { iMod (fupd_atleast_intro_mask'); last iApply Hfupd_atleast. done. }
  rewrite uPred_fupd_atleast_eq /uPred_fupd_atleast_def.
  iMod ("H" with "[$]") as "[Hw [HE >H']]"; iFrame.
Qed.

(*
Lemma step_fupd_atleastN_soundness `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n |={⊤,∅}=> ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_atleast_plain_soundness ⊤ ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  destruct n as [|n].
  - iApply fupd_atleast_plainly_mask_empty. iMod "H" as %?; auto.
  - iDestruct (step_fupd_atleastN_wand _ _ _ _ (|={⊤}=> ⌜φ⌝)%I with "H []") as "H'".
    { by iApply fupd_atleast_plain_mask_empty. }
    rewrite -step_fupd_atleastN_S_fupd_atleast.
    iMod (step_fupd_atleastN_plain with "H'") as "Hφ". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "Hφ".
Qed.

Lemma step_fupd_atleastN_soundness' `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupd_atleastN_soundness _ n).
  iIntros (Hinv). iPoseProof (Hiter Hinv) as "Hiter".
  iApply (step_fupd_atleastN_wand with "Hiter"). by iApply fupd_atleast_mask_weaken.
Qed.
 *)
End fupd_atleast.


Section test.
Context `{!invG Σ}.
Context `{HT: AbsolutelyTimeless (iPropI Σ) P}.

Goal ∀ E, (|2={E}=> P) ⊢ |2={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E, (|={E}=> P) ⊢ |1={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E, (|={E}=> P) ⊢ |2={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E1 E2 E3, (|={E1, E2}=> P) ∗ (|2={E2,E3}=> True) ⊢ |2={E1, E3}=> P.
Proof using HT.
  iIntros (???) "(HP&HT)". iMod "HP". iMod "HT". eauto.
Qed.

Goal ◇_2 P -∗ ◇_2 P.
Proof using HT.
  iIntros "HP". iMod "HP". iModIntro. auto.
Qed.

Goal ▷^2 P -∗ ◇_2 P.
Proof using HT.
  iIntros "HP". by iMod "HP".
Qed.

Goal ∀ E, ▷^2 P -∗ |2={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E, ▷▷ P -∗ |2={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E, ▷ P -∗ |2={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

Goal ∀ E, ▷ P -∗ |1={E}=> P.
Proof using HT.
  iIntros (?) "HP". by iMod "HP".
Qed.

End test.
