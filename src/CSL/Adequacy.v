Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre.
Require Import CSL.Crash.



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
Record adequate {OpT T} {Λ: Layer OpT} (s : stuckness) (e1 : proc OpT T) (σ1 : Λ.(State))
    (φ : T → Λ.(State) → Prop) := {
  adequate_result σ2 res :
    Λ.(exec) e1 σ1 σ2 res → ∃ v, res = existT _ v ∧ φ v σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   Λ.(exec_partial) e1 σ1 σ2 t2 →
   e2 ∈ t2 → (is_Some (to_val (projT2 e2)) ∨ reducible (projT2 e2) σ2)
}.

(* Adequacy for execution with a recovery procedure *)
Record recv_adequate {OpT T R} {Λ: Layer OpT} (s : stuckness) (e1 : proc OpT T)
       (rec: proc OpT R) (σ1 : Λ.(State)) (φ : T → Λ.(State) → Prop) (φrec: Λ.(State) → Prop) := {
  recv_adequate_normal_result σ2 res :
    Λ.(exec) e1 σ1 σ2 res → ∃ v, res = existT _ v ∧ φ v σ2;
  recv_adequate_result σ2 res :
    Λ.(rexec) e1 (rec_singleton rec) σ1 σ2 res → φrec σ2;
  (* TODO: this does not guarantee non-stuckness during recovery because rexec_partial
     throws away the thread pool; but it seems
     that we prefer explicit error states rather than partiality anyway *)
  (*
  recv_adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   (Λ.(exec_partial) e1 σ1 σ2 t2 ∨ Λ.(rexec_partial) e1 (rec_singleton rec) σ1 σ2 t2) →
   e2 ∈ t2 → (is_Some (to_val (projT2 e2)) ∨ reducible (projT2 e2) σ2)
   *)
}.

(*
Theorem adequate_tp_safe {OpT T} {Λ: Layer OpT} (e1 : proc OpT T) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  Λ.(step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.
*)

Section adequacy.
Context {OpT: Type → Type}.
Context `{Λ: Layer OpT}.
Context `{irisG OpT Λ Σ}.
(*
Implicit Types e : expr Λ.
*)
Implicit Types P Q : iProp Σ.
(*
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).
*)

Notation world' E σ := (wsat ∗ ownE E ∗ state_interp σ)%I (only parsing).
Notation world σ := (world' ⊤ σ) (only parsing).

Notation wptp s t := ([∗ list] ef ∈ t, WP (projT2 ef) @ s; ⊤ {{ _, True }})%I.

Lemma wp_step {T} s E e1 σ1 (e2: proc OpT T) σ2 efs Φ :
  Λ.(exec_step) e1 σ1 σ2 (e2, efs) →
  world' E σ1 ∗ WP e1 @ s; E {{ Φ }}
  ==∗ ▷ |==> ◇ (world' E σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "[(Hw & HE & Hσ) H]".
  destruct (to_val e1) eqn:Hval.
  { apply of_to_val in Hval. rewrite /of_val in Hval. subst.
    destruct H as [Hσ Heq]. inversion Heq; subst.
    iModIntro; rewrite wp_unfold //=. by iFrame.
  }
  rewrite // uPred_fupd_eq.
  iMod ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iMod ("H" $! e2 σ2 efs with "[//] [$Hw $HE]") as ">(Hw & HE & H)".
  iIntros "!> !>". by iMod ("H" with "[$Hw $HE]") as ">($ & $ & $)".
Qed.

Lemma wptp_step {T} s e1 t1 t2 σ1 σ2 Φ :
  Λ.(exec_pool) ((existT T e1) :: t1) σ1 σ2 t2 →
  world σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ==∗ ∃ e2 t2', ⌜t2 = existT T e2 :: t2'⌝ ∗ ▷ |==> ◇ (world σ2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep%exec_pool_equiv_alt) "(HW & He & Ht)".
  destruct Hstep as [T' e1' e2' efs [|? t1'] t2' Heq1 Heq2 Hstep]. rewrite //= in Heq1 Heq2.
  - inversion Heq1 as [[Heq1' Heq2']]; subst.
    assert (e1 = e1') by eauto with *; subst.
    iExists e2', (t2' ++ efs); iSplitR; first eauto.
    iFrame "Ht". iApply wp_step; eauto with iFrame.
  - simplify_eq/=.
    iExists e1, (t1' ++ existT _ e2' :: t2' ++ efs); iSplitR; first by eauto.
    iDestruct "Ht" as "($ & He' & $)". iFrame "He".
    iApply wp_step; eauto with iFrame.
Qed.

Lemma wptp_steps {T} s n e1 t1 t2 σ1 σ2 Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 σ2 t2 →
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
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 σ2 (existT T' (of_val v2') :: t2) →
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
  world' E σ -∗ WP e @ E {{ Φ }} ==∗ ▷ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "(Hw&HE&Hσ) H".
  destruct (to_val e) as [v|] eqn:?.
  { iIntros "!> !> !%". left. by exists v. }
  rewrite uPred_fupd_eq. iMod ("H" with "Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  iIntros "!> !> !%". by right.
Qed.

Lemma wptp_safe {T T'} n (e1: proc OpT T) (e2: proc OpT T') t1 t2 σ1 σ2 Φ :
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 σ2 t2 →
  existT T' e2 ∈ t2 →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp NotStuck t1
  ⊢ ▷^(S (S n)) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
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
  bind_rep_n n (Λ.(exec_pool)) (existT T e1 :: t1) σ1 σ2 t2 →
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

Theorem wp_strong_adequacy {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗ ⌜φ v σ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros σ' (T'&v') Hexec.
    destruct Hexec as ([|(?&e')]&?&Hpartial&Hcheck).
    { inversion Hcheck. }
    destruct e'; inversion Hcheck; subst.
    inversion H1; subst.
    unfold exec_partial in Hpartial.
    apply bind_star_inv_rep_n in Hpartial as (n&Hpartial).
    assert (v' = v).
    { eapply Eqdep.EqdepTheory.inj_pair2 in H1; eauto. }
    subst.
    cut (∃ v0 : T, existT T (@of_val OpT _ v0) = existT T0 (of_val v) ∧ φ v0 σ').
    { intros (vnew&?&?). exists vnew; split; auto. inversion H0. congruence. }
    eapply (soundness (M:=iResUR Σ) _ (S (S n))).
    iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _).
    rewrite {1}uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iApply (@wptp_result _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
  - destruct s; last done.
    intros t2 σ2 (T'&e2') _ Hpartial Hin.
    unfold exec_partial in Hpartial.
    apply bind_star_inv_rep_n in Hpartial as (n&Hpartial).
    eapply (soundness (M:=iResUR Σ) _ (S (S n))).
    iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _).
    rewrite uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iApply (@wptp_safe _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
Qed.

Theorem wp_adequacy {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy _ _)=> Hinv.
  iMod Hwp as (stateI) "[Hσ H]". iExists stateI. iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iMod (fupd_intro_mask' ⊤ ∅) as "_"; auto.
Qed.

Theorem wp_invariance {T} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 ={⊤,∅}=∗ ⌜φ⌝))%I) →
  Λ.(exec_partial) e σ1 σ2 t2 →
  φ.
Proof.
  intros Hwp Hpartial.
  apply bind_star_inv_rep_n in Hpartial as (n&Hpartial).
  eapply (soundness (M:=iResUR Σ) _ (S (S n))).
  iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _).
  rewrite {1}uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
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
  Λ.(exec_partial) e σ1 σ2 t2 →
  φ.
Proof.
  intros Hwp. eapply wp_invariance; first done.
  intros Hinv. iMod (Hwp Hinv) as (stateI) "(? & ? & Hφ)".
  iModIntro. iExists stateI. iFrame. iIntros "Hσ".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  iMod (fupd_intro_mask') as "_"; last by iModIntro. solve_ndisj.
Qed.

Import RelationNotations.

Theorem wp_recovery_adequacy {T R} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 φ φinv (φrec : Λ.(State) → Prop) :
  (* normal execution *)
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ ={⊤,∅}=∗ ⌜φ v σ⌝ }}
         ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ ⌜φinv σ2'⌝))%I) →
  (* recovery *)
  (∀ `{Hinv : invG Σ} σ1 σ1' (Hφinv: φinv σ1) (Hcrash: Λ.(crash_step) σ1 σ1' tt),
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1' ∗ WP rec @ s; ⊤ {{ _, ∀ σ, stateI σ ={⊤, ∅}=∗ ⌜φrec σ⌝ }}
         ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ ⌜φinv σ2'⌝))%I) →
  recv_adequate s e rec σ1 φ φrec.
Proof.
  intros Hwp_e Hwp_rec. split.
  - intros σ2 ? Hexec. eapply wp_strong_adequacy; eauto.
    intros Hinv.
    iMod Hwp_e as (stateI) "[Hσ [H Hφ]]". iExists stateI. iIntros "{$Hσ} {$H} !> "; auto.
  - rewrite /rexec/exec_recover => σ2 [] Hrexec.
    eapply rimpl_elim in Hrexec; last first.
    { setoid_rewrite exec_seq_partial_singleton.
      setoid_rewrite <-bind_assoc at 2.
      setoid_rewrite seq_unit_sliding.
      setoid_rewrite bind_assoc.
      reflexivity.
    }
    destruct Hrexec as (tp&σhalt&Hpartial&Hrec).
    (* Show that φ is preserved after halt of e *)
    assert (Hφ: φinv σhalt).
    { eapply wp_invariance; eauto.
      intros Hinv.
      iMod Hwp_e as (stateI) "[Hσ [H Hφ]]". iExists stateI. iIntros "{$Hσ} !>".
      iSplitL "H"; last by iApply "Hφ".
      iApply (wp_mono with "H"); eauto.
    }
    clear Hpartial Hwp_e.
    destruct Hrec as ([]&σhalt_rec&Hhd&Hrest).
    (* Show that φ is preserved after crash + halt of rec *)
    assert (Hφhalt_rec: φinv σhalt_rec).
    {
      clear Hrest.
      induction Hhd as [σhalt_rec []| x y z [] [] Hhd Hstar IH]; eauto.
      eapply IH; eauto.
      clear IH Hstar.
      destruct Hhd as ([]&σcrash&Hcrash&Hhalt).
      destruct Hhalt as (tp'&?&Hpartial&[]); subst.
      eapply wp_invariance; eauto.
      intros Hinv.
      iMod Hwp_rec as (stateI) "[Hσ [H Hφ]]"; eauto. iExists stateI. iIntros "{$Hσ} !>".
      iSplitL "H"; last by iApply "Hφ".
      iApply (wp_mono with "H"); eauto.
    }
    clear Hhd Hφ.
    destruct Hrest as ([]&σcrash&Hcrash&(tp'&?&Hexec&[])); subst.
    edestruct (wp_strong_adequacy _ s rec σcrash (λ _ σ2, φrec σ2)) as (Had&?); eauto; last first.
    { edestruct Had; intuition eauto. }
    intros Hinv.
    iMod Hwp_rec as (stateI) "[Hσ [H Hφ]]"; eauto.
    iExists stateI. iIntros "{$Hσ} {$H} !> "; auto.
Qed.

Theorem wp_recovery_invariance {T R} OpT Σ Λ `{invPreG Σ} s (e: proc OpT T) (rec: proc OpT R)
        σ1 σ2 t2 (φ ρ : Λ.(State) → Prop) :
  (* φ is an invariant of normal execution *)
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ s; ⊤ {{ _, True }} ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ ⌜φ σ2'⌝))%I) →
  (* φ is an invariant of recovery execution *)
  (∀ `{Hinv : invG Σ} σ1 σ1' (Hφ: φ σ1) (Hcrash: Λ.(crash_step) σ1 σ1' tt),
     (|={⊤}=> ∃ stateI : State Λ → iProp Σ,
       let _ : irisG OpT Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1' ∗ WP rec @ s; ⊤ {{ _, True }} ∗ (∀ σ2', stateI σ2' ={⊤,∅}=∗ ⌜φ σ2'⌝))%I) →
  (∀ σ, φ σ → ρ σ) →
  (∀ σ1 σ2, φ σ1 → Λ.(crash_step) σ1 σ2 tt → ρ σ2) →
  Λ.(rexec_partial) e (rec_singleton rec) σ1 σ2 t2 →
  ρ σ2.
Proof.
  intros Hwp_e Hwp_rec Himpl Hcrash_impl Hpartial.
  unfold rexec_partial, exec_recover_partial in Hpartial.
  destruct Hpartial as (tp&σhalt&Hpartial&Hrec).
  (* Show that φ is preserved after halt of e *)
  assert (Hφ: φ σhalt).
  { eapply wp_invariance; eauto.
    intros Hinv.
    iMod Hwp_e as (stateI) "[Hσ [H Hφ]]". iExists stateI. iIntros "{$Hσ} {$H} !> Hσ".
      by iApply "Hφ".
  }
  clear Hpartial Hwp_e.
  eapply rimpl_elim in Hrec; last first.
  { setoid_rewrite exec_seq_partial_singleton.
    setoid_rewrite seq_sliding.
    setoid_rewrite <-bind_assoc at 1.
    reflexivity. }
  destruct Hrec as ([]&σhalt_rec&Hhd&Hrest).
  (* Show that φ is preserved after crash + halt of rec *)
  assert (Hφ_halt: ∀ σhalt σhalt_rec,
             φ σhalt ->
             (_ <- Λ.(crash_step); exec_halt Λ rec) σhalt σhalt_rec () ->
             φ σhalt_rec).
  {
    intros ??? ([]&σcrash&Hcrash&Hhalt).
    destruct Hhalt as (tp'&?&Hpartial&[]); subst.
    eapply wp_invariance; eauto.
    intros Hinv.
    iMod Hwp_rec as (stateI) "[Hσ [H Hφ]]"; eauto. iExists stateI. iIntros "{$Hσ} {$H} !> Hσ".
      by iApply "Hφ".
  }
  assert (Hrec: φ σhalt_rec) by eauto.
  clear Hwp_rec. clear Hhd.
  revert σhalt Hrec Hφ.
  induction Hrest as [σhalt_rec []| x y z [] []]; eauto.
Qed.