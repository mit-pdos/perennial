From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Export invariants.
From Perennial.program_logic Require Import invariants_mutable staged_invariant_alt.
From Perennial.base_logic.lib Require Import wsat.
Set Default Proof Using "Type".
Import uPred.

(*

  A simplified version of "crash borrows" that can essentially only opened
  over an atomic step. Essentially, we allocate a special kind of invariant
  that has two parameters, a mutable "P" part and an immutable "Pc" part. We
  can think of the invariant as a non-duplicable "box" in which some P is
  stored, with the property that P always implies Pc.

  When you open the box across an atomic step, you get ▷ P. When closing the
  box, you do not have to put ▷ P back in. Instead, you may update the mutable
  parameter to ▷ P' and put ▷ P' in, so long as ▷ P' implies ▷ Pc.

  More precisely, rather than putting in such a P' that implies Pc, we put in
  P' ∧ Pc.

  If you try to encode this on top of standard Iris invariants using saved
  predicates, then unfortunately  when opening the box you will only get
  ▷ ▷ P. This is a problem because even if P is timeless, ▷ P is not.  We can
  work around this using later credits (see new/proof/own_crash.v for an
  alternate encoding that uses this route).

  Instead, we can use the mechanism of "invariant schemas" and mutable
  invariants that Perennial supports to avoid this issue. This file uses the
  schema that we previously developed in wp_to_wpc.v for showing a generic
  HOCAP wp can be converted to a HOCAP wpc.

*)



Section own_crash_inv.
Context `{!invGS Σ}.
Context `{!crashGS Σ}.
Context `{!stagedG Σ}.

Definition own_crash_sch : bi_schema :=
  (bi_sch_or (bi_sch_and (bi_sch_var_mut 0) (bi_sch_except_0 (bi_sch_fupd ∅ ∅ (bi_sch_var_fixed 0))))
             (bi_sch_or (bi_sch_sep (bi_sch_var_fixed 2) (bi_sch_var_fixed 3))
                        (bi_sch_var_fixed 1))).

Lemma own_crash_sch_interp_weak k P Qs_mut γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> Qs_mut) own_crash_sch ⊣⊢
                   let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
                      (((Qs ∧ ◇ |k,Some O={∅}=> ▷ P) ∨ ((▷ C ∗ ▷ staged_pending (3/4)%Qp γ)
                       ∨ (▷ staged_done γ))))%I.
Proof.
  remember (S k) as n eqn:Heq.
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
  rewrite Heq.
  erewrite (bi_sch_fupd_interp); last first.
  { rewrite ?bi_schema_interp_unfold /= //=. }
  rewrite list_lookup_fmap. by f_equiv.
Qed.

Lemma own_crash_sch_interp_strong k P Q γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> [Q]) own_crash_sch ⊣⊢
                      (((▷ Q ∧ ◇ |k,Some O={∅}=> ▷ P) ∨ ((▷ C ∗ ▷ staged_pending (3/4)%Qp γ)
                       ∨ (▷ staged_done γ))))%I.
Proof.
  remember (S k) as n eqn:Heq.
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
  rewrite Heq.
  erewrite (bi_sch_fupd_interp); last first.
  { rewrite ?bi_schema_interp_unfold /= //=. }
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
Qed.

Definition own_crash_redeem `{!invGS Σ} N Pc : iProp Σ :=
  ∃ γ, inv_mut 1 N own_crash_sch [Pc; staged_done γ; C; staged_pending (3/4)%Qp γ] ∗
       staged_pending (3/4)%Qp γ.

Definition own_crash `{!invGS Σ} N P Pc : iProp Σ :=
  ∃ γ, inv_mut 1 N own_crash_sch [Pc; staged_done γ; C; staged_pending (3/4)%Qp γ] ∗
       inv_mut_full 1 N own_crash_sch [P] [Pc; staged_done γ; C; staged_pending (3/4)%Qp γ] ∗
       staged_pending (1/4)%Qp γ.

Lemma own_crash_redeem_cfupd N E Pc :
  ↑N ⊆ E →
  own_crash_redeem N Pc -∗ |C={E}=> ▷ Pc.
Proof.
  iIntros (?) "H".
  iDestruct "H" as (γ) "(#Hinv&Hpend34)".
  iMod (inv_mut_acc with "Hinv") as (Qs) "(H&Hclo)"; first auto.
  iIntros "HC".
  rewrite own_crash_sch_interp_weak /=.
  iDestruct "H" as "[(_&>H)|[Hfalse1|Hfalse2]]".
  * iApply (fupd_level_fupd _ _ _ (S 0)).
    iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def).
    iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
    iMod (fupd_split_level_le with "H") as "H"; first lia.
    iMod "Hclo''".
    iSpecialize ("Hclo" with "[HC Hpend34]").
    { iRight. iLeft. iFrame. }
    iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def) in "Hclo".
    iMod "Hclo". iFrame "H"; done.
  * iDestruct "Hfalse1" as "(>_&>?)". iDestruct (pending34_pending34 with "[$] [$]") as "[]".
  * iDestruct "Hfalse2" as ">?". iDestruct (pending_done with "[$] [$]") as "[]".
Qed.

Lemma own_crash_alloc_weak N E P Pc :
  ▷ P ∧ ▷ Pc -∗ |={E}=> own_crash_redeem N Pc ∗ own_crash N P Pc.
Proof.
  iIntros "HP".
  iMod (pending_alloc) as (γpending) "Hpending".
  iMod (inv_mut_alloc (S 0) N _ own_crash_sch ([ Pc; staged_done γpending; C; staged_pending (3/4)%Qp γpending])%I [P] with "[HP]") as "(#Hinv&Hfull)".
  {  rewrite own_crash_sch_interp_strong.
     iLeft. iSplit.
     - iDestruct "HP" as "($&_)".
     - iModIntro. iModIntro. iNext. iDestruct "HP" as "(_&$)".
  }
  iDestruct (pending_split34 with "Hpending") as "(Hpend34&Hpend14)".
  iModIntro.
  iSplitR "Hfull Hpend14".
  - iExists γpending. rewrite /own_crash_redeem. iFrame. iExact "Hinv".
  - iExists γpending. rewrite /own_crash. iFrame. iExact "Hinv".
Qed.

Lemma own_crash_open N E P Pc :
  ↑N ⊆ E →
  own_crash N P Pc -∗
  |NC={E, E ∖ ↑N}=> ▷ P ∗ ∀ P', ▷ P' ∧ ▷ Pc -∗ |={E ∖ ↑N, E}=> own_crash N P' Pc.
Proof.
  iIntros (Hin) "H".
  iDestruct "H" as (γ) "(#Hinv&Hown&Hpend)".
  rewrite /own_crash.
  rewrite ncfupd_eq /ncfupd_def. iIntros (q) "HNC".
  iMod (inv_mut_full_acc with "Hown") as "(H&Hclo)"; first auto.
  rewrite ?own_crash_sch_interp_strong.
  iDestruct "H" as "[HQ|Hfalse]"; last first.
  { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
    * iDestruct (NC_C with "[$] [$]") as "[]".
    * iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iDestruct "HQ" as "(HQ&_)".
  iModIntro.
  iFrame "HQ HNC".
  iIntros (P') "HP'".
  iMod ("Hclo" $! [P'] with "[HP']") as "Hfull".
  { rewrite own_crash_sch_interp_strong. iLeft. iSplit; first auto.
    - iDestruct "HP'" as "($&_)".
    - iModIntro. iModIntro. iDestruct "HP'" as "(_&$)".
  }
  iModIntro. iFrame. iFrame "Hinv".
Qed.

End own_crash_inv.

(*

   In many cases, what we have in the box is always (Φ a) for some a,
   and the crash predicate is just ∃ a, Φ a. That is, we know that we
   have Φ for *some* a after the crash, but lose knowledge of which a.

   This next section defines specialized lemmas/definitions for
   working with this case.

*)

Section own_crash_ex.

Context `{!invGS Σ}.
Context `{!crashGS Σ}.
Context `{!stagedG Σ}.

Context {A : Type}.

Implicit Types Φ : A → iProp Σ.
Implicit Types a : A.

Definition own_crash_ex N Φ a : iProp Σ :=
  own_crash N (Φ a) (∃ a, Φ a).

Definition own_crash_ex_redeem N Φ : iProp Σ :=
  own_crash_redeem N (∃ a, Φ a).

Lemma own_crash_ex_alloc N E Φ a :
  ▷ (Φ a) -∗ |={E}=> own_crash_ex_redeem N Φ ∗ own_crash_ex N Φ a.
Proof.
  iIntros "HΦ".
  iApply own_crash_alloc_weak.
  iSplit; by eauto with iFrame.
Qed.

Lemma own_crash_ex_redeem_cfupd N E Φ :
  ↑N ⊆ E →
  own_crash_ex_redeem N Φ -∗ |C={E}=> ▷ ∃ a, Φ a.
Proof. apply own_crash_redeem_cfupd. Qed.

Lemma own_crash_ex_open N E Φ a :
  ↑N ⊆ E →
  own_crash_ex N Φ a -∗
  |NC={E, E ∖ ↑N}=> ▷ Φ a ∗ ∀ a', ▷ Φ a' -∗ |={E ∖ ↑N, E}=> own_crash_ex N Φ a'.
Proof.
  iIntros (?) "Hex".
  iMod (own_crash_open with "Hex") as "H"; first done.
  iDestruct "H" as "($&Hclo)".
  iModIntro. iIntros (a') "HΦa'".
  iMod ("Hclo" $! (Φ a') with "[HΦa']") as "H".
  { iSplit; by eauto with iFrame. }
  by iFrame.
Qed.

End own_crash_ex.

Section wpc.
Context `{!irisGS Λ Σ, !generationGS Λ Σ, stagedG Σ}.

(* Demo of how allocating a own_crash gives you ▷ of the "crash invariant" in the postcondition *)

Lemma wpc_own_crash_alloc_weak s E N (P Pc : iProp Σ) (e : expr Λ) Φ Φc :
  ↑N ⊆ E →
  ▷ P ∧ ▷ Pc -∗
  (own_crash N P Pc -∗ WPC e @ s ; E {{ Φ }} {{ ▷ Pc -∗ Φc }}) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "HP Hwp".
  iMod (own_crash_alloc_weak N E P Pc with "[$]") as "(Hredeem&H)".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit.
  { eauto. }
  { iIntros "Hpc".
    iMod (own_crash_redeem_cfupd with "Hredeem"); first by auto.
    iModIntro. iApply "Hpc". auto.
  }
Qed.

Lemma wpc_own_crash_ex_alloc {A} s E N (Φex : A → iProp Σ) (a : A) (e : expr Λ) Φ Φc :
  ↑N ⊆ E →
  ▷ Φex a -∗
  (own_crash_ex N Φex a -∗ WPC e @ s ; E {{ Φ }} {{ ▷ (∃ a, Φex a) -∗ Φc }}) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "HP Hwp".
  iMod (own_crash_ex_alloc N E Φex a with "[$]") as "(Hredeem&H)".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpc_strong_mono with "Hwp"); auto.
  iSplit.
  { eauto. }
  { iIntros "Hpc". iMod (own_crash_redeem_cfupd with "Hredeem"); first by auto.
    iModIntro. iApply "Hpc". auto.
  }
Qed.

End wpc.
