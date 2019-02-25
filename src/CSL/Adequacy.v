Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre.

From stdpp Require Import namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Global functor setup *)
Definition invΣ : gFunctors :=
  #[GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
    GFunctor coPset_disjUR;
    GFunctor (gset_disjUR positive)].

Class invPreG (Σ : gFunctors) : Set := WsatPreG {
  inv_inPreG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inPreG :> inG Σ coPset_disjR;
  disabled_inPreG :> inG Σ (gset_disjR positive);
}.

Instance subG_invΣ {Σ} : subG invΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

(* Allocation *)
Lemma wsat_alloc `{invPreG Σ} : (|==> ∃ _ : invG Σ, wsat ∗ ownE ⊤)%I.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap _ _))) as (γI) "HI"; first done.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ _ _ γI γE γD).
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.


(* Program logic adequacy *)
Definition adequate_internal {Σ} {OpT T} {Λ: Layer OpT} (s : stuckness)
           (e1 : proc OpT T) (σ1 : Λ.(State)) (φ : T → Λ.(State) → iProp Σ) k : iProp Σ :=
  ((∀ (n: nat) σ2 res,
    ⌜ Λ.(exec_n) e1 n σ1 (Val σ2 res) ⌝ →
    (Nat.iter (S k + S (S n)) (λ P, |==> ▷ P)%I (∃ v, ⌜ res = existT _ v ⌝ ∧ φ v σ2))) ∧
  ((∀ (n: nat),
     ⌜ s = NotStuck ⌝ →
     ⌜ Λ.(exec_partial_n) e1 n σ1 Err ⌝ →
     (▷^(S k + S (S n)) False))))%I.

Record adequate {OpT T} {Λ: Layer OpT} (s : stuckness) (e1 : proc OpT T) (σ1 : Λ.(State))
    (φ : T → Λ.(State) → Prop) := {
   adequate_result σ2 res :
    Λ.(exec) e1 σ1 (Val σ2 res) → ∃ v, res = existT _ v ∧ φ v σ2;
    adequate_not_stuck :
    s = NotStuck → ¬ Λ.(exec_partial) e1 σ1 Err
 }.

(* Adequacy for execution with a recovery procedure *)
Definition recv_adequate_internal {Σ} {OpT T R} {Λ: Layer OpT} (s : stuckness) (e1 : proc OpT T)
       (rec: proc OpT R) (σ1 : Λ.(State))
       (φ : T → Λ.(State) → iProp Σ) (φrec: Λ.(State) → iProp Σ) k :=
  (* recv_adequate_internal_normal_result n σ2 res  : *)
  ((∀ n σ2 res,
    ⌜ Λ.(exec_n) e1 n σ1 (Val σ2 res) ⌝ →
    (Nat.iter (S k + (S (S n))) (λ P, |==> ▷ P)%I (∃ v, ⌜ res = existT _ v ⌝ ∧ φ v σ2)))
   ∧
   (∀ n σ2 res,
    ⌜ Λ.(rexec_n) e1 rec n σ1 (Val σ2 res) ⌝ →
    (Nat.iter (S k + (5 + n))) (λ P, |==> ▷ P)%I (φrec σ2))
   ∧
  ((∀ (n: nat),
     ⌜ s = NotStuck ⌝ →
     ⌜ Λ.(rexec_n) e1 rec n σ1 Err ⌝ →
     (▷^(S k + (5 + n)) False))))%I.

Record recv_adequate {OpT T R} {Λ: Layer OpT} (s : stuckness) (e1 : proc OpT T)
       (rec: proc OpT R) (σ1 : Λ.(State)) (φ : T → Λ.(State) → Prop) (φrec: Λ.(State) → Prop) := {
   recv_adequate_normal_result σ2 res :
     Λ.(exec) e1 σ1 (Val σ2 res) → ∃ v, res = existT _ v ∧ φ v σ2;
   recv_adequate_result σ2 res :
     Λ.(rexec) e1 (rec_singleton rec) σ1 (Val σ2 res) → φrec σ2;
   recv_adequate_not_stuck :
     s = NotStuck →
     ¬ Λ.(rexec) e1 (rec_singleton rec) σ1 Err
 }.

Record proc_seq_adequate {OpT T R} {Λ: Layer OpT} (s : stuckness) (es : proc_seq OpT T)
       (rec: proc OpT R) (σ1 : Λ.(State)) (φ : T → Λ.(State) → Prop) (φrec: Λ.(State) → Prop) := {
   proc_seq_adequate_normal_result σ2 res :
     Λ.(proc_exec_seq) es (rec_singleton rec) σ1 (Val σ2 res) →
     match res with
     | Normal e => ∃ v, e = existT _ v ∧ φ v σ2
     | Recovered _ => φrec σ2
     end;
   proc_seq_adequate_not_stuck :
     s = NotStuck →
     ¬ Λ.(proc_exec_seq) es (rec_singleton rec) σ1 Err
 }.

Section adequacy.
Context {OpT: Type → Type}.
Context `{Λ: Layer OpT}.
Context `{irisG OpT Λ Σ}.
Implicit Types P Q : iProp Σ.

Notation world' E σ := (wsat ∗ ownE E ∗ state_interp σ)%I (only parsing).
Notation world σ := (world' ⊤ σ) (only parsing).

Notation wptp s t := ([∗ list] ef ∈ t, WP (projT2 ef) @ s; ⊤ {{ _, True }})%I.

Lemma wp_step {T} s E e1 σ1 (e2: proc OpT T) σ2 efs Φ :
  Λ.(exec_step) e1 σ1 (Val σ2 (e2, efs)) →
  world' E σ1 ∗ WP e1 @ s; E {{ Φ }}
  ==∗ ▷ |==> ◇ (world' E σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "[(Hw & HE & Hσ) H]".
  destruct (to_val e1) eqn:Hval.
  { apply of_to_val in Hval. rewrite /of_val in Hval. subst.
    inversion H; subst.
  }
  rewrite // uPred_fupd_eq.
  iMod ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iMod ("H" $! e2 σ2 efs with "[//] [$Hw $HE]") as ">(Hw & HE & H)".
  iIntros "!> !>". by iMod ("H" with "[$Hw $HE]") as ">($ & $ & $)".
Qed.

Lemma wptp_step {T} s e1 t1 t2 σ1 σ2 Φ :
  Λ.(exec_pool) ((existT T e1) :: t1) σ1 (Val σ2 t2) →
  world σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ==∗ ∃ e2 t2', ⌜t2 = existT T e2 :: t2'⌝ ∗ ▷ |==> ◇ (world σ2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep%exec_pool_equiv_alt_val) "(HW & He & Ht)".
  inversion Hstep as [T' e1' e2' ? efs ? [|? t1'] t2' Heq1 Heq2 Heq3 Hstep'|]; last by congruence.
  rewrite //= in Heq1 Heq2 Heq3.
  - inversion Heq1 as [[Heq1' Heq2']]; subst.
    assert (e1 = e1') by eauto with *; subst.
    inversion Heq3; subst; eauto.
    iExists e2', (t2' ++ efs); iSplitR; first eauto.
    iFrame "Ht". iApply wp_step; eauto with iFrame.
  - simplify_eq/=.
    iExists e1, (t1' ++ existT _ e2' :: t2' ++ efs); iSplitR; first by eauto.
    iDestruct "Ht" as "($ & He' & $)". iFrame "He".
    iApply wp_step; eauto with iFrame.
Qed.

Lemma wptp_steps {T} s n e1 t1 t2 σ1 σ2 Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 t2) →
  world σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ⊢
  Nat.iter (S n) (λ P, |==> ▷ P) (∃ e2 t2',
    ⌜t2 = existT T e2 :: t2'⌝ ∗ world σ2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  revert e1 t1 t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 t2 σ1 σ2.
  { inversion_clear 1; iIntros "(?&?&?)"; subst. iExists e1, t1; iFrame; auto. }
  iIntros (Hsteps) "H". destruct Hsteps as (t1'&σ1'&Hexec&Hsteps).
  iMod (wptp_step with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq.
  iModIntro; iNext; iMod "H" as ">?". by iApply IH.
Qed.

Lemma bupd_iter_mono n P Q :
  (P -∗ Q) -∗ Nat.iter n (λ P, |==> ▷ P)%I P -∗ Nat.iter n (λ P, |==> ▷ P)%I Q.
Proof.
  iIntros "HPQ". iInduction n as [|n IH] "IH".
  - simpl. iApply "HPQ".
  - simpl. iIntros "Hiter". iMod "Hiter". iModIntro. iNext. iApply ("IH" with "HPQ Hiter").
Qed.

Lemma bupd_iter_le n1 n2 P :
  n1 ≤ n2 → Nat.iter n1 (λ P, |==> ▷ P)%I P -∗ Nat.iter n2 (λ P, |==> ▷ P)%I P.
Proof.
  iIntros (Hle). induction Hle; auto.
  - simpl. iIntros "Hiter". iModIntro. iNext.  iApply (IHHle with "Hiter").
Qed.

Lemma wptp_steps_state_inv {T} s n e1 t1 t2 σ1 σ2 Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 t2) →
  world σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ⊢
  Nat.iter (S n) (λ P, |==> ▷ P) (world σ2).
Proof.
  iIntros (?) "H". iPoseProof (wptp_steps with "H") as "H"; eauto.
  iApply (bupd_iter_mono with "[] H"); eauto.
  iIntros "H". iDestruct "H" as (??) "(?&?&?)"; iFrame.
Qed.

Lemma bupd_iter_laterN_mono n P Q `{!Plain Q} :
  (P ⊢ Q) → Nat.iter n (λ P, |==> ▷ P)%I P ⊢ ▷^n Q.
Proof.
  intros HPQ. induction n as [|n IH]=> //=. by rewrite IH bupd_plain.
Qed.

Lemma bupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |==> ▷ P) Q ⊢ Nat.iter n (λ P, |==> ▷ P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  by rewrite bupd_frame_l {1}(later_intro R) -later_sep IH.
Qed.

Lemma wptp_result {T T'} s n e1 t1 v2' t2 σ1 σ2 φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 (existT T' (of_val v2') :: t2)) →
  world σ1 ∗ WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ ={⊤,∅}=∗ ⌜φ v σ⌝ }} ∗ wptp s t1
  ⊢ ▷^(S (S n)) ⌜∃ v2, existT T (@of_val OpT _ v2) = existT T' (@of_val OpT _ v2') ∧ φ v2 σ2⌝.
Proof.
  intros. rewrite wptp_steps // laterN_later. apply: bupd_iter_laterN_mono.
  iDestruct 1 as (e2 t2' ?) "((Hw & HE & Hσ) & H & _)"; simplify_eq.
  assert (Ret v2' = e2) by eauto with *; subst.
  iDestruct (wp_value_inv' with "H") as "H". rewrite uPred_fupd_eq.
  iMod ("H" with "[$]") as ">(Hw & HE & H)".
  iExists v2'. iMod ("H" with "Hσ [$]") as ">(_ & _ & %)"; auto.
Qed.

Lemma wp_safe {T} E (e: proc OpT T) σ Φ :
  world' E σ -∗ WP e @ E {{ Φ }} ==∗ ▷ ⌜ non_errorable e σ ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "(Hw&HE&Hσ) H".
  destruct (to_val e) as [v|] eqn:?.
  { iIntros "!> !> !%". by eapply val_non_errorable. }
  rewrite uPred_fupd_eq. iMod ("H" with "Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  done.
Qed.

Lemma wptp_result' {T T'} s n e1 t1 v2' t2 σ1 σ2 φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 (existT T' (of_val v2') :: t2)) →
  world σ1 ∗ WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ ={⊤,∅}=∗ φ v σ }} ∗ wptp s t1
  ⊢ Nat.iter (S (S n)) (λ P, |==> ▷ P)%I (∃ v2, ⌜ existT T (@of_val OpT _ v2) = existT T' (@of_val OpT _ v2') ⌝ ∧ φ v2 σ2).
Proof.
  intros. rewrite wptp_steps // (Nat_iter_S_r ((S n))). iApply bupd_iter_mono.
  iDestruct 1 as (e2 t2' ?) "((Hw & HE & Hσ) & H & _)"; simplify_eq.
  assert (Ret v2' = e2) by eauto with *; subst.
  iDestruct (wp_value_inv' with "H") as "H". rewrite uPred_fupd_eq.
  iMod ("H" with "[$]") as ">(Hw & HE & H)".
  iExists v2'. iMod ("H" with "Hσ [$]") as ">(_ & _ & ?)"; auto.
Qed.

Lemma wptp_safe {T T'} n (e1: proc OpT T) (e2: proc OpT T') t1 t2 σ1 σ2 Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 t2) →
  existT T' e2 ∈ t2 →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp NotStuck t1
  ⊢ ▷^(S (S n)) ⌜ non_errorable e2 σ2 ⌝.
Proof.
  intros ? He2. rewrite wptp_steps // laterN_later. apply: bupd_iter_laterN_mono.
  iDestruct 1 as (e2' t2' ?) "(Hw & H & Htp)"; simplify_eq.
  apply elem_of_cons in He2 as [Heq|?].
  - inversion Heq; subst.  assert (e2 = e2') as <- by eauto with *.
    iMod (wp_safe with "Hw H") as "$".
  - iMod (wp_safe with "Hw [Htp]") as "$".
    iPoseProof (big_sepL_elem_of with "Htp") as "H"; eauto.
Qed.

Lemma wptp_invariance {T} s n e1 t1 t2 σ1 σ2 φ Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 (Val σ2 t2) →
  (state_interp σ2 ={⊤,∅}=∗ ⌜φ⌝) ∗ world σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ⊢ ▷^(S (S n)) ⌜φ⌝.
Proof.
  intros ?. rewrite wptp_steps // bupd_iter_frame_l laterN_later.
  apply: bupd_iter_laterN_mono.
  iIntros "[Hback H]"; iDestruct "H" as (e2' t2' ->) "[(Hw&HE&Hσ) _]".
  rewrite uPred_fupd_eq.
  iMod ("Hback" with "Hσ [$Hw $HE]") as "> (_ & _ & $)"; auto.
Qed.
End adequacy.

Theorem adequacy_int_to_ext {T} OpT Σ Λ s (e: proc OpT T) σ φ k:
  adequate_internal (Σ := Σ) (Λ := Λ) s e σ (fun v σ => ⌜ φ v σ ⌝)%I k →
  adequate s e σ φ.
Proof.
  intros Hinternal. split.
  * intros ?? Hexec. apply exec_equiv_exec_n in Hexec as (n&?).
    eapply (soundness (M:=iResUR Σ) _ (S k + S (S n))).
    iDestruct Hinternal as "(Hres&_)".
    iApply bupd_iter_laterN_mono; first by reflexivity; eauto.
    iApply bupd_iter_mono; last first.
    { iApply "Hres"; eauto. }
    { eauto. }
  * intros ? Hexec. apply exec_partial_equiv_exec_partial_n in Hexec as (n&?).
    eapply (soundness (M:=iResUR Σ) _ (S k + S (S n))).
    iDestruct Hinternal as "(_&Hnstuck)". iApply "Hnstuck"; eauto.
Qed.

Transparent lifted_crash_step.

Lemma lifted_crash_non_err {OpT} (Λ: Layer OpT):
  ∀ (s1 : Proc.State) (ret : Return Proc.State ()), lifted_crash_step Λ s1 ret → ret ≠ Err.
Proof.
  intros ??. rewrite /lifted_crash_step. destruct ret; auto.
  destruct s1. inversion 1.
  * inversion H0.
  * destruct H0 as (?&(?&?)&?&?). by apply crash_non_err in H1.
Qed.

Theorem recv_adequacy_int_to_ext {T R} OpT Σ Λ (e: proc OpT T) (rec: proc OpT R) σ φ φrec k:
  recv_adequate_internal (Σ := Σ) (Λ := Λ) NotStuck e rec σ
                         (fun v σ => ⌜ φ v σ ⌝)%I (fun σ => ⌜ φrec σ ⌝)%I k →
  recv_adequate NotStuck e rec σ φ φrec.
Proof.
  intros Hinternal.
  assert (¬ rexec Λ e (rec_singleton rec) σ Err).
  {
    intros Hrexec.
    apply rexec_equiv_rexec_n'_err in Hrexec as (n&?Hrexec);
      last by eapply lifted_crash_non_err.
    eapply (soundness (M:=iResUR Σ) _ (S k + (5 + n))).
    iDestruct Hinternal as "(_&Hnstuck)". iApply "Hnstuck"; eauto.
  }
  split; auto.
  - intros ?? Hexec.
    apply exec_equiv_exec_n in Hexec as (n&?).
    eapply (soundness (M:=iResUR Σ) _ (S k + S (S n))).
    iDestruct Hinternal as "(Hres&_&_)".
    iApply bupd_iter_laterN_mono; first by reflexivity; eauto.
    iApply bupd_iter_mono; last first.
    { iApply "Hres"; eauto. }
    { eauto. }
  - intros ? [] Hexec.
    apply rexec_equiv_rexec_n'_val in Hexec as (n&?); eauto using lifted_crash_non_err.
    eapply (soundness (M:=iResUR Σ) _ (S k + (5 + n))).
    iDestruct Hinternal as "(_&Hres&_)".
    iApply bupd_iter_laterN_mono; first by reflexivity; eauto.
    iApply bupd_iter_mono; last first.
    { iApply "Hres"; eauto. }
    { eauto. }
Qed.

Lemma exec_partial_n_err_alt {T} OpT (Λ: Layer OpT) (e: proc OpT T) n σ:
  exec_partial_n Λ e n σ Err →
  ∃ n' tp1 tp2 Terr err σ2,
  n' ≤ n ∧
  exec_step Λ err σ2 Err ∧
  bind_rep_n n' (exec_pool Λ) [existT T e] σ (Val σ2 (tp1 ++ existT Terr err :: tp2)).
Proof.
  intros Hpartial.
  assert (bind_rep_r_n n (exec_pool Λ) [existT T e] σ Err) as Hpartial_r.
  { apply bind_rep_lr_n in Hpartial. intuition. }
  apply bind_rep_r_n_err_inv in Hpartial_r as (n'&t2&σ2&Hle&Hpartial'&Hexec).
  apply bind_rep_lr_n_val in Hpartial'.
  apply exec_pool_equiv_alt_err in Hexec.
  inversion Hexec; subst; try congruence.
  repeat eexists; eauto.
Qed.

Theorem wp_strong_adequacy_internal {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ φ k:
  (∀ `{Hinv : invG Σ},
     Nat.iter k (λ P, |==> ▷ P)%I (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗  φ v σ  }})%I) ⊢
  adequate_internal s e σ φ k.
Proof.
  iIntros "Hwp"; iSplit.
  - iIntros (n σ' (T'&v') Hexec).
    destruct Hexec as (tp&Hpartial).
    subst. simpl.
    rewrite Nat_iter_add.
    iMod wsat_alloc as (Hinv) "[Hw HE]". iSpecialize ("Hwp" $! _).
    iModIntro. iNext.
    iApply (bupd_iter_mono k with "[Hw HE] [Hwp]"); last by iApply "Hwp".
    iIntros "Hwp". rewrite {1}uPred_fupd_eq.
    iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iPoseProof (@wptp_result' _ _ _ (IrisG _ _ _ Hinv Istate) with "[-]") as "H".
    { eauto. }
    { iFrame. rewrite //=. }
    iApply (bupd_iter_mono (S (S n)) with "[] H").
    iIntros "H". iDestruct "H" as (v'' Heq) "?". inversion Heq; subst.
    iExists v''; iSplit; auto.
  - destruct s; last done.
    iIntros (n ? Hpartial).
    edestruct (exec_partial_n_err_alt Λ e) as (n'&tp1&typ2&Terr&err&σ2&Hle&Hexec&Hpartial');
      eauto.
    iAssert (▷^(S k + S (S n')) ⌜@non_errorable _ _ Λ err σ2⌝)%I with "[Hwp]" as "Herr"; last first.
    { iApply (laterN_le (S k+ S (S n'))); first by lia.
      iApply laterN_mono; last by iApply "Herr". iPureIntro; eauto. }
    rewrite laterN_plus.
    iApply bupd_iter_laterN_mono; first by reflexivity.
    iMod wsat_alloc as (Hinv) "[Hw HE]". iSpecialize ("Hwp" $! _).
    iModIntro. iNext.
    iApply (bupd_iter_mono k with "[Hw HE] [Hwp]"); last by iApply "Hwp".
    iIntros "Hwp". rewrite {1}uPred_fupd_eq.
    iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iApply (@wptp_safe _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
    set_solver+.
Qed.

Theorem wp_strong_adequacy {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ φ k:
  (∀ `{Hinv : invG Σ},
     Nat.iter k (λ P, |==> ▷ P)%I (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗ ⌜ φ v σ ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp. unshelve (eapply @adequacy_int_to_ext); eauto.
  iApply wp_strong_adequacy_internal. iIntros (Hinv). iApply Hwp.
Qed.

Theorem wp_adequacy {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ φ k:
  (∀ `{Hinv : invG Σ},
     Nat.iter k (λ P, |==> ▷ P)%I (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy _ _ _ _ k)=> Hinv.
  iPoseProof (Hwp _) as "Hwp".
  iApply (bupd_iter_mono with "[] Hwp").
  iIntros "Hwp'".
  iMod "Hwp'" as (stateI) "[Hσ H]". iExists stateI. iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iMod (fupd_intro_mask' ⊤ ∅) as "_"; auto.
Qed.

Theorem wp_invariance {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ1 t2 σ2 φ k:
  (∀ `{Hinv : invG Σ},
     Nat.iter k (λ P, |==> ▷ P)%I (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 ={⊤,∅}=∗ ⌜φ⌝))%I) →
  Λ.(exec_partial) e σ1 (Val σ2 t2) →
  φ.
Proof.
  intros Hwp Hpartial.
  apply bind_star_inv_rep_n in Hpartial as (n&Hpartial).
  eapply (soundness (M:=iResUR Σ) _ (S k + S (S n))).
  rewrite laterN_plus.
  iApply bupd_iter_laterN_mono; first by reflexivity.
  iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _).
  iModIntro. iNext.
  iApply (bupd_iter_mono k with "[Hw HE] []"); last by iApply Hwp.
  iIntros "Hwp". rewrite {1}uPred_fupd_eq.
  iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
  iDestruct "Hwp" as (Istate) "(HIstate & Hwp & Hclose)".
  iApply (@wptp_invariance _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
Qed.

(* An equivalent version that does not require finding [fupd_intro_mask'], but
can be confusing to use. *)
Corollary wp_invariance' {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  Λ.(exec_partial) e σ1 (Val σ2 t2) →
  φ.
Proof.
  intros Hwp. eapply wp_invariance with (k := O); first done.
  intros Hinv. iMod (Hwp Hinv) as (stateI) "(? & ? & Hφ)".
  iModIntro. iExists stateI. iFrame. iIntros "Hσ".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  iMod (fupd_intro_mask') as "_"; last by iModIntro. solve_ndisj.
Qed.

Import RelationNotations.

Lemma exec_rec_iter_split {R} OpT (Λ: Layer OpT) (rec: proc OpT R) σhalt ret:
  (_ <- seq_star (_ <- Λ.(lifted_crash_step); exec_halt Λ rec); _ <- Λ.(lifted_crash_step); exec_halt Λ rec)
    σhalt ret →
  ∃ σcrash σrec : Λ.(State),
    seq_star (_ <- Λ.(lifted_crash_step); exec_halt Λ rec) σhalt (Val σcrash ())
    ∧ Λ.(lifted_crash_step) σcrash (Val σrec ())
    ∧ exec_halt Λ rec σrec ret.
Proof.
  intros Hrec. destruct ret as [b t|].
  {
    destruct Hrec as ([]&σhalt_rec&Hhd&([]&?&?&?)).
    do 2 eexists; split_and!; eauto.
  }
  {
    destruct Hrec as [Hstar_err|([]&σhalt_rec&Hhd&Hrest)].
    - remember Err as ret eqn:Heq.
      revert Heq; induction Hstar_err; intros; try congruence; subst.
      * edestruct IHHstar_err as (σcrash&σrec_err&Hstar&?); auto.
        exists σcrash, σrec_err; split; auto.
        econstructor; eauto.
      * destruct H as [|([]&σ&?&?)].
        { exfalso. eapply lifted_crash_non_err; eauto. }
        exists x, σ; split; auto.
        econstructor.
    - destruct Hrest as [|([]&σ&?&?)].
      { exfalso. eapply lifted_crash_non_err; eauto. }
      do 2 eexists; split_and!; eauto.
  }
Qed.

Lemma rexec_n_iter_split {R} OpT (Λ: Layer OpT) (rec: proc OpT R) σhalt ret n2 n3:
  (_ <- seq_star_exec_steps Λ rec n2; _ <- Λ.(lifted_crash_step); _ <- exec_n Λ rec n3; pure ())
           σhalt ret →
  ∃ (σcrash σrec : Λ.(State)) n2' n3',
    (n2 + n3 >= n2' + n3')%nat ∧
    (seq_star_exec_steps Λ rec n2') σhalt (Val σcrash ())
    ∧ Λ.(lifted_crash_step) σcrash (Val σrec ())
    ∧ (_ <- exec_n Λ rec n3'; pure ()) σrec ret.
Proof.
  intros Hrec. destruct ret as [b t|].
  {
    destruct Hrec as ([]&σhalt_rec&Hhd&([]&?&?&?)).
    do 4 eexists; split_and!; eauto.
  }
  {
    destruct Hrec as [Hstar_err|([]&σhalt_rec&Hhd&Hrest)].
    - remember Err as ret eqn:Heq.
      revert Heq; induction Hstar_err; intros; try congruence; subst.
      * edestruct IHHstar_err as (σcrash&σrec_err&n2'&n3'&Heq&Hstar&?); auto.
        eexists σcrash, σrec_err, _, _; split; last first.
        { split; eauto. econstructor; eauto. }
        { lia. }
      * do 4 eexists; split; last first.
        { split. econstructor. split. eauto. left; eauto. }
        { lia. }
    - destruct Hrest as [|([]&σ&?&?)].
      { exfalso. eapply lifted_crash_non_err; eauto. }
      do 4 eexists; split_and!; eauto.
  }
Qed.

Definition recv_idemp {R OpT} Σ (Λ: Layer OpT) `{invPreG Σ} s (rec: proc OpT R)
        φinv φrec :=
     (□ (∀ `{Hinv : invG Σ} σ1 σ1' (Hcrash: Λ.(lifted_crash_step) σ1 (Val σ1' tt)),
           (φinv σ1 ={⊤}=∗
                ∃ stateI : State Λ → iProp Σ,
                  let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
                  stateI σ1'
                         ∗ WP rec @ s; ⊤ {{ _, ∀ σ, stateI σ ={⊤, ∅}=∗ φrec σ }}
                         ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ φinv σ2'))))%I.

Lemma recv_idemp_adequacy_inv {R} OpT Σ (Λ: Layer OpT) `{invPreG Σ} s (rec: proc OpT R)
      φinv φrec σhalt σcrash k0:
  seq_star_exec_steps Λ rec k0 σhalt (Val σcrash tt) →
  recv_idemp s rec φinv φrec -∗
  (|==> ◇ φinv σhalt) -∗
  Nat.iter (S k0) (λ P, |==> ▷ P)%I (|==> ◇ φinv σcrash).
Proof.
  iIntros (Hstar) "#Hwp_rec Hhalt".
  remember (Val σcrash ()) as ret eqn:Heq.
  iInduction Hstar as [| k0 σhalt σhalt' σmid ret ? m Hcrash Hrep Hind|] "IH"; last by congruence.
  { inversion Heq; subst. iIntros "!> !>"; auto. }
  inversion Heq; subst.

  rewrite (Nat_iter_S (S m + S k)).
  rewrite Nat_iter_add.
  iMod wsat_alloc as (Hinv'') "[Hw HE]".
  iSpecialize ("Hwp_rec" $! Hinv'').
  iSpecialize ("Hwp_rec" $! _ _ Hcrash).
  rewrite uPred_fupd_eq.
  iMod "Hhalt". iModIntro. iMod "Hhalt". iNext.
  iMod ("Hwp_rec" with "Hhalt [$Hw $HE]") as ">(Hw & HE & Hrest)".
  iDestruct "Hrest" as (stateI') "(Hs&Hwp&Hinv)".
  iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
  { eapply Hrep. }
  { iFrame. done. }
  iApply (bupd_iter_mono with "[Hinv] H").
  iIntros "(Hw&HE&Hstate)".
  iApply "IH"; auto.
  iSpecialize ("Hinv" with "[Hstate]"); eauto.
  rewrite /uPred_fupd_def.
    by iMod ("Hinv" with "[$Hw $HE]") as ">(?&?&$)".
Qed.

Definition wp_recovery {T R OpT} Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 φ φrec k :=
  (Nat.iter k (λ P, |==> ▷ P)%I
    (∃ (φinv : Λ.(State) → iProp Σ), ∀ `{Hinv : invG Σ},
     (* normal execution *)
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗ φ v σ }}
                 ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ φinv σ2')
     ∗ recv_idemp s rec φinv φrec)))%I.

Theorem wp_recovery_adequacy_internal {T R} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 φ (φrec : Λ.(State) → iProp Σ) k:
  s = NotStuck →
  wp_recovery s e rec σ1 φ φrec k ⊢
  recv_adequate_internal s e rec σ1 φ φrec k.
Proof.
  iIntros (?) "Hwp". iSplit; [| iSplit].
  - iIntros (? σ2 ? Hexec).
    iApply (wp_strong_adequacy_internal with "[Hwp]"); last eauto.
    iIntros (Hinv). iApply (bupd_iter_mono with "[] Hwp"). iIntros "Hwp".
    iDestruct "Hwp" as (φinv) "Hwp".
    iSpecialize ("Hwp" $! Hinv).
    iMod "Hwp" as (stateI) "(Hσ&Hwp_e&?&_)".
    iExists stateI. iIntros "{$Hσ} !> "; auto.
  - iIntros (n0 σ2 [] Hrexec_n).
    inversion Hrexec_n as [? ? n k0 n3 Heq Hrexec]; subst.
    clear Hrexec_n.
    destruct Hrexec as (tp&σhalt&Hpartial&Hrec).
    destruct Hrec as ([]&σcrash&Hstar&Hfin).
    destruct Hfin as ([]&σcrash'&Hcrash&Hfin).
    destruct Hfin as (?&?&Hexec&Hp).
    inversion Hp; subst. clear Hp.

    iPoseProof (wp_strong_adequacy_internal NotStuck rec σcrash' (λ _ s, φrec s)
                                        (S k + S n + S k0 ) with "[Hwp]") as "(Had&_)"; last first.
    {
      assert ((S k + (5 + (n + k0 + n3))) = (S (S k + S n + S k0) + S (S n3)))%nat as Heq.
      { lia. }
      iApply bupd_iter_mono; last first.
      { rewrite Heq. iApply "Had". eauto. }
      iIntros "H". iDestruct "H" as (? ?) "$".
    }


    iIntros (Hinv).
    rewrite Nat_iter_add.
    rewrite Nat_iter_add.
    iMod wsat_alloc as (Hinv') "[Hw HE]".
    iApply (bupd_iter_mono with "[Hw HE] Hwp"). iIntros "Hwp".
    iDestruct "Hwp" as (φinv) "Hwp".
    iSpecialize ("Hwp" $! Hinv').
    rewrite uPred_fupd_eq.
    iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hrest)".
    iDestruct "Hrest" as (stateI) "(Hσ&Hwp_e&Hinv&#Hwp_rec)".
    iAssert (Nat.iter (S n) (λ P, |==> ▷ P)%I (|==> ◇ φinv σhalt))%I with "[Hw HE Hσ Hwp_e Hinv]"
      as "Hσhalt".
    {
      iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
      { eapply Hpartial. }
      { iFrame. done. }
      iApply (bupd_iter_mono with "[Hinv] H").
      iIntros "(Hw&HE&Hstate)". iSpecialize ("Hinv" with "Hstate").
      iMod ("Hinv" with "[$Hw $HE]") as "(?&?&$)"; auto.
    }
    iApply (bupd_iter_mono with "[] Hσhalt"); iIntros "Hσhalt".

    clear Hpartial.

    iAssert (Nat.iter (S k0) (λ P, |==> ▷ P)%I (|==> ◇ φinv σcrash))%I with "[Hσhalt]" as "Hinv'".
    { unshelve (iApply recv_idemp_adequacy_inv; eauto); eauto. }

    iApply (bupd_iter_mono with "[] Hinv'"); iIntros ">>Hinv'".
    iSpecialize ("Hwp_rec" $! Hinv σcrash σcrash' Hcrash with "Hinv'").
    iMod "Hwp_rec" as (stateI'') "[Hσ [H _]]"; eauto.
    iExists stateI''. iIntros "{$Hσ} !> "; auto.

  - iIntros (n _ Hrexec_n).
    inversion Hrexec_n as [?? n1 n2 n3 Heq Hrexec_n']; subst.
    destruct Hrexec_n' as [|(tp&σhalt&Hpartial&Hrec)].
    {
      iApply laterN_le; last first.
      { iApply (wp_strong_adequacy_internal with "[Hwp]"); eauto.
        iIntros (Hinv).
        iApply (bupd_iter_mono with "[] Hwp"). iIntros "Hwp".
        iDestruct "Hwp" as (φinv) "Hwp".
        iSpecialize ("Hwp" $! Hinv).
        iMod "Hwp" as (stateI) "(Hσ&Hwp_e&?&_)".
        iExists stateI. iIntros "{$Hσ} !> "; auto.
      }
      { lia. }
    }
    edestruct (@rexec_n_iter_split)
        as (σcrash&σrec_err&k0&n'&Hle&Hstar&Hcrash&Herr); eauto.
    apply bind_pure_no_err in Herr.

    iPoseProof (wp_strong_adequacy_internal NotStuck rec σrec_err (λ _ s, φrec s)
                                        (S k + S n1 + S k0) with "[Hwp]") as "(_&Hnst)"; last first.
    { iApply laterN_le; last iApply "Hnst"; eauto.
      lia.
    }

    iIntros (Hinv).
    rewrite Nat_iter_add.
    rewrite Nat_iter_add.
    iMod wsat_alloc as (Hinv') "[Hw HE]".
    iApply (bupd_iter_mono with "[Hw HE] Hwp"). iIntros "Hwp".
    iDestruct "Hwp" as (φinv) "Hwp".
    iSpecialize ("Hwp" $! Hinv').
    rewrite uPred_fupd_eq.
    iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hrest)".
    iDestruct "Hrest" as (stateI) "(Hσ&Hwp_e&Hinv&#Hwp_rec)".
    iAssert (Nat.iter (S n1) (λ P, |==> ▷ P)%I (|==> ◇ φinv σhalt))%I with "[Hw HE Hσ Hwp_e Hinv]"
      as "Hσhalt".
    {
      iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
      { eapply Hpartial. }
      { iFrame. done. }
      iApply (bupd_iter_mono with "[Hinv] H").
      iIntros "(Hw&HE&Hstate)". iSpecialize ("Hinv" with "Hstate").
      iMod ("Hinv" with "[$Hw $HE]") as "(?&?&$)"; auto.
    }
    iApply (bupd_iter_mono with "[] Hσhalt"); iIntros "Hσhalt".

    clear Hpartial Hrec.

    iAssert (Nat.iter (S k0) (λ P, |==> ▷ P)%I (|==> ◇ φinv σcrash))%I with "[Hσhalt]" as "Hinv'".
    { unshelve (iApply recv_idemp_adequacy_inv; eauto); eauto. }

    iApply (bupd_iter_mono with "[] Hinv'"); iIntros ">>Hinv'".
    iSpecialize ("Hwp_rec" $! Hinv σcrash σrec_err Hcrash with "Hinv'").
    iMod "Hwp_rec" as (stateI'') "[Hσ [H _]]"; eauto.
    iExists stateI''. iIntros "{$Hσ} !> "; auto.
Qed.

Theorem wp_recovery_adequacy {T R} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 φ (φrec : Λ.(State) → Prop) k:
  s = NotStuck →
  wp_recovery s e rec σ1 (fun v σ => ⌜ φ v σ ⌝)%I (fun σ => ⌜ φrec σ ⌝)%I k →
  recv_adequate s e rec σ1 φ φrec.
Proof.
  intros ? Hwp. subst. unshelve (eapply @recv_adequacy_int_to_ext); eauto.
  iApply wp_recovery_adequacy_internal; eauto.  iApply Hwp.
Qed.

(* FIXME: add outer iter of k *)
(*
Theorem wp_recovery_invariance {T R} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 φ φrec φinv ρ :
  (∀ `{Hinv : invG Σ},
     (* normal execution *)
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗ ⌜ φ v σ ⌝ }}
       ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ φinv σ2' ∗ ⌜ ρ σ2' ⌝)
     ∗
     (* recovery execution *)
     □ (∀ `{Hinv : invG Σ} σ1 σ1' (Hcrash: Λ.(crash_step) σ1 (Val σ1' tt)),
     (φinv σ1 ={⊤}=∗ ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1' ∗ WP rec @ s; ⊤ {{ _, ∀ σ, stateI σ ={⊤, ∅}=∗ ⌜ φrec σ ⌝ }}
         ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ φinv σ2' ∗ ⌜ ρ σ2' ⌝)))))%I →
  s = NotStuck →
  (∀ σ2 t2, Λ.(rexec_partial) e (rec_singleton rec) σ1 (Val σ2 t2) → ρ σ2)
    ∧ recv_adequate s e rec σ1 φ φrec.
Proof.
  intros Hwp ?.
  assert (recv_adequate s e rec σ1 φ φrec).
  {
    eapply recv_adequacy_int_to_ext.
    eapply wp_recovery_adequacy_internal with (φinv0 := φinv); first eauto.
    - intros. iIntros. iPoseProof (Hwp $! Hinv) as "Hwp".
      iMod "Hwp" as (stateI) "(Hσ&Hwp_e&Hφ&#Hwp_rec)".
      iModIntro. iExists stateI. iFrame.
      iSplitR "Hwp_rec".
      * iIntros. iMod ("Hφ" with "[$]") as "($&?)"; auto.
      * iIntros. iModIntro. iIntros.
        iMod ("Hwp_rec" with "[//] [$]") as (stateI') "[Hσ [H Hφ]]"; eauto.
        iExists stateI'.
        iIntros "{$Hσ} {$H} !>". iIntros. iMod ("Hφ" with "[$]") as "($&?)"; auto.
    - eauto.
  }
  split; auto. intros σ2 [] Hpartial.
  unfold rexec_partial, exec_recover_partial in Hpartial.

  eapply requiv_no_err_elim in Hpartial; first last.
  { intros Herr. apply rexec_partial_err_rexec_err in Herr.
    eapply recv_adequate_not_stuck; eauto. }
  { setoid_rewrite exec_seq_partial_singleton.
    setoid_rewrite <-bind_assoc at 2.
    setoid_rewrite <-bind_assoc at 2.
    setoid_rewrite <-seq_unit_sliding_equiv.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    reflexivity.
  }
  destruct Hpartial as (tp&σhalt&Hpartial&Hrec).
  destruct Hrec as ([]&σcrash&Hstar&([]&σrec&Hcrash&Hrec)).
  destruct Hrec as (?&?&Hrec&Hpure). inversion Hpure; subst.
  apply bind_star_inv_rep_n in Hpartial as (n&Hpartial).
  apply seq_star_exec_steps_intro in Hstar as (k&Hstar).

  eapply @wp_invariance with (k := (S n + S k)%nat); eauto.
  intros Hinv.
  rewrite Nat_iter_add.
  iMod wsat_alloc as (Hinv') "[Hw HE]".
  iPoseProof (Hwp $! Hinv') as "Hwp".
  rewrite uPred_fupd_eq.
  iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hrest)".
  iDestruct "Hrest" as (stateI) "(Hσ&Hwp_e&Hinv&#Hwp_rec)".

  iAssert (Nat.iter (S n) (λ P, |==> ▷ P)%I (|==> ◇ φinv σhalt))%I with "[Hw HE Hσ Hwp_e Hinv]"
    as "Hσhalt".
  {
    iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
    { eapply Hpartial. }
    { iFrame. done. }
    iApply (bupd_iter_mono with "[Hinv] H").
    iIntros "(Hw&HE&Hstate)". iSpecialize ("Hinv" with "Hstate").
    iMod ("Hinv" with "[$Hw $HE]") as "(?&?&($&?))"; auto.
  }
  iApply (bupd_iter_mono with "[] Hσhalt"); iIntros "Hσhalt".

  iClear "Hwp".
  clear Hpartial.

  iAssert (Nat.iter (S k) (λ P, |==> ▷ P)%I (|==> ◇ φinv σcrash))%I with "[Hσhalt]" as "Hinv'".
  {
    clear Hcrash Hrec σ2 Hpure.
    iInduction Hstar as [| σhalt σhalt' σmid ret σcrash k m Hcrash Hrep Hind ] "IH".
    { iIntros "!> !>"; auto. }

    rewrite (Nat_iter_S (S m + S k)).
    rewrite Nat_iter_add.
    iMod wsat_alloc as (Hinv'') "[Hw HE]".
    iSpecialize ("Hwp_rec" $! Hinv'').
    iSpecialize ("Hwp_rec" $! _ _ Hcrash).
    rewrite uPred_fupd_eq.
    iMod "Hσhalt". iModIntro. iMod "Hσhalt". iNext.
    iMod ("Hwp_rec" with "Hσhalt [$Hw $HE]") as ">(Hw & HE & Hrest)".
    iDestruct "Hrest" as (stateI') "(Hs&Hwp&Hinv)".
    iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
    { eapply Hrep. }
    { iFrame. done. }
    iApply (bupd_iter_mono with "[Hinv] H").
    iIntros "(Hw&HE&Hstate)".
    iApply "IH"; auto.
    iSpecialize ("Hinv" with "[Hstate]"); eauto.
    rewrite /uPred_fupd_def.
    by iMod ("Hinv" with "[$Hw $HE]") as ">(?&?&($&?))".
  }


  iApply (bupd_iter_mono with "[] Hinv'"); iIntros ">>Hinv'".
  iSpecialize ("Hwp_rec" $! Hinv σcrash _ Hcrash with "Hinv'").
  iMod "Hwp_rec" as (stateI'') "[Hσ [H Hinv]]"; eauto.
  iExists stateI''. iIntros "{$Hσ} !> "; auto.
  iSplitL "H".
  - iApply wp_wand_l; iFrame. iIntros; auto.
  - iIntros. iMod ("Hinv" with "[$]") as "(?&$)"; auto.
Qed.
*)

Fixpoint wp_proc_seq {T R} OpT Σ Λ `{invPreG Σ} s (es: proc_seq OpT T) (rec: proc OpT R)
        σ1 φ (φrec : Λ.(State) → iProp Σ) : iProp Σ :=
  match es with
  | Proc_Seq_Final e => wp_recovery s e rec σ1 φ φrec O
  | @Proc_Seq_Bind _ _ T0 e es' =>
    wp_recovery s e rec σ1
                (λ v σ2, wp_proc_seq s (es' (Normal (existT T0 v))) rec σ2 φ φrec)
                (λ σ2, wp_proc_seq s (es' (Recovered (existT _ tt))) rec σ2 φ φrec)
                O
  end.

(* TODO: there is a lot of silly case splitting because of how these
   lemmas are structured *)
(*
Theorem wp_proc_seq_adequacy {T R} OpT Σ Λ `{invPreG Σ} s (es: proc_seq OpT T) (rec: proc OpT R)
        σ1 φ φrec k:
  Nat.iter k (λ P, |==> ▷ P)%I
             (wp_proc_seq Λ s es rec σ1 (λ v σ2, ⌜ φ v σ2 ⌝%I) (λ σ2, ⌜ φrec σ2 ⌝%I)) →
  s = NotStuck →
  proc_seq_adequate s es rec σ1 φ φrec.
Proof.
  intros Hwp ->.
  split.
  - revert k σ1 Hwp. induction es => k σ1 Hwp σ2 res.
    * destruct 1 as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
         eapply recv_adequate_normal_result with (s := NotStuck); eauto.
         unshelve (eapply recv_adequacy_int_to_ext); eauto.
         unshelve (iApply wp_recovery_adequacy_internal); eauto.
         iApply Hwp.
      ** destruct Hrecv as (v&?&Hrexec&Hpure). inversion Hpure; subst.
         eapply recv_adequate_result with (s := NotStuck); eauto.
         unshelve (eapply recv_adequacy_int_to_ext); eauto.
         unshelve (iApply wp_recovery_adequacy_internal); eauto.
         iApply Hwp.
    * destruct 1 as (res0&σ1'&Hhd&Hrest).
      destruct Hhd as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
         eapply exec_equiv_exec_n in Hexec as (n&Hexec).
         iPoseProof Hwp as "Hwp".
         eapply H0; eauto.
         eapply wp_recovery_adequacy_internal in Hwp; auto.
         eapply recv_adequate_internal_normal_result in Hwp; eauto.
         eapply H0; eauto.
         iApply (bupd_iter_mono); last iApply Hwp.
         iIntros "Hrec". iDestruct "Hrec" as (v' Hp) "Hrec".
         subst. iApply "Hrec".
      ** destruct Hrecv as ([]&?&Hrexec&Hpure). inversion Hpure; subst.
         eapply wp_recovery_adequacy_internal in Hwp; auto.
         eapply rexec_equiv_rexec_n' in Hrexec as (n&Hexec).
         { eapply recv_adequate_internal_result in Hwp as Hwp; eauto.
           eapply H0; eauto. }
         { eapply recv_adequate_internal_not_stuck in Hwp as Hwp; eauto. }
  - revert k σ1 Hwp. induction es => k σ1 Hwp _.
    * destruct 1 as [Hnorm%bind_pure_no_err|Hrecv%bind_pure_no_err].
      ** eapply exec_err_rexec_err in Hnorm.
         eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
      ** eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
    * destruct 1 as [[Hnorm%bind_pure_no_err|Hrec%bind_pure_no_err]|Htl].
      ** eapply exec_err_rexec_err in Hnorm.
         eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
      ** eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
      ** destruct Htl as (?&σ1'&[Hnorm|Hrec]&?).
         *** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
             eapply wp_recovery_adequacy_internal in Hwp; auto.
             eapply exec_equiv_exec_n in Hexec as (n&Hexec).
             eapply recv_adequate_internal_normal_result in Hwp; eauto.
             eapply H0; eauto.
             iApply (bupd_iter_mono); last iApply Hwp.
             iIntros "Hrec". iDestruct "Hrec" as (v' Hp) "Hrec".
             subst. iApply "Hrec".
         *** destruct Hrec as ([]&?&Hexec&Hpure). inversion Hpure; subst.
             eapply wp_recovery_adequacy_internal in Hwp; auto.
             eapply rexec_equiv_rexec_n' in Hexec as (n&Hexec).
             { eapply recv_adequate_internal_result in Hwp as Hwp; eauto.
               eapply H0; eauto. }
             { eapply recv_adequate_internal_not_stuck in Hwp as Hwp; eauto. }
Qed.
*)

(*
Theorem wp_proc_seq_adequacy' {T R} OpT Σ Λ `{invPreG Σ} s (es: proc_seq OpT T) (rec: proc OpT R)
        σ1 φ φrec k:
  Nat.iter k (λ P, |==> ▷ P)%I
             (wp_proc_seq Λ s es rec σ1 (λ v σ2, ⌜ φ v σ2 ⌝%I) (λ σ2, ⌜ φrec σ2 ⌝%I)) →
  s = NotStuck →
  proc_seq_adequate s es rec σ1 φ φrec.
Proof.
  intros Hwp ->.
  revert k σ1 Hwp. induction es => k σ1 Hwp.
  - split.
    * destruct 1 as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
         eapply recv_adequate_normal_result; eauto.
         eapply recv_adequacy_int_to_ext.
         eapply wp_recovery_adequacy_internal; eauto.
      ** destruct Hrecv as (v&?&Hrexec&Hpure). inversion Hpure; subst.
         eapply recv_adequate_result; eauto.
         eapply recv_adequacy_int_to_ext.
         eapply wp_recovery_adequacy_internal; eauto.
    * intros ?. destruct 1 as [Hnorm%bind_pure_no_err|Hrecv%bind_pure_no_err].
      ** eapply exec_err_rexec_err in Hnorm.
         eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
      ** eapply recv_adequate_internal_not_stuck; eauto.
         eapply wp_recovery_adequacy_internal; eauto.
  - split. intros.
    * destruct H1 as (res0&σ1'&Hhd&Hrest).
      destruct Hhd.
*)