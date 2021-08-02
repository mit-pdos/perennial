From Perennial.program_logic Require Import invariants_mutable.
From Perennial.program_proof Require Import disk_prelude. (* FIXME: make this disk-independent *)
From Perennial.base_logic.lib Require Import wsat.

(* This file explores ways to promote a HOCAP wp spec that relies on Perennial 1 style
   for crash safety into a Peony/Perennial 2 HOCAP spec.

   In particular, in the former, one usually has a fupd as a precondition to "update" some
   abstract state, which looks like

    (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (transition σ) ∗ Φ #())

   The issue, when it comes to crash safety, is that the resource used to
   *prove* this fupd, might itself be a durable resource. Thus if a wpc calls a
   wp with the above kind of HOCAP spec, it may not be able to prove its crash
   condition.

   The Peony/Perennial 2 style is to instead have something like

    <disc> ▷ Φc ∧ (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (transition σ) ∗ <disc> ▷ Φc ∧ Φ #())

   The idea is that if we crash *before* the fupd, we use the left side of the
   outer conjunct to prove a Φc crash condition, while if we crash after the
   fupd, we use the left side of the inner conjunct.

   This file shows that style 1 can be promoted to style 2 under some conditions.
*)

Section goose.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Axiom (state : Type).
Axiom (transition : state → state).
Axiom (e: expr).

Section wp_spec.

Axiom is_foo1 : forall (N: namespace) (P: state → iProp Σ) (γ: gname), iProp Σ.

Context (N: namespace).

(* Assume this is the wp_spec that we want to promote *)
Lemma wp_spec P Φ γ :
  is_foo1 N P γ ∗
  (∀ σ, ▷ P σ -∗ |NC={⊤ ∖ ↑N}=> ▷ P (transition σ) ∗ Φ #()) -∗
  WP e {{ Φ }}.
Proof. Admitted.

End wp_spec.

Section wpc_spec.

Context (N: namespace).
Definition N1 := N.@"1".
Definition N2 := N.@"2".

Definition mysch : bi_schema :=
  (bi_sch_or (bi_sch_and (bi_sch_var_mut 0) (bi_sch_except_0 (bi_sch_fupd ∅ ∅ (bi_sch_var_fixed 0))))
             (bi_sch_or (bi_sch_sep (bi_sch_var_fixed 2) (bi_sch_var_fixed 3))
                        (bi_sch_var_fixed 1))).
Lemma mysch_interp_weak k P Qs_mut γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> Qs_mut) mysch ⊣⊢
                   let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
                      (((Qs ∧ ◇ |k,Some O={∅}=> ▷ P) ∨ ((▷ C ∗ ▷ staged_pending (3/4)%Qp γ)
                       ∨ (▷ staged_done γ))))%I.
Proof.
  remember (S k) as n eqn:Heq.
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
  rewrite Heq.
  erewrite (bi_sch_fupd_interp); last first.
  { rewrite ?bi_schema_interp_unfold /= //=. }
  rewrite list_lookup_fmap. f_equiv.
Qed.

Lemma mysch_interp_strong k P Q γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> [Q]) mysch ⊣⊢
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

Lemma wpc_spec P Φ Φc `{HT: Timeless _ Φc} γ k :
  is_foo1 N1 P γ ∗
  (<disc> Φc ∧ (∀ σ, ▷ P σ -∗ |NC={⊤ ∖ ↑ N}=> ▷ P (transition σ) ∗ (<disc> Φc ∧ Φ (#())))) -∗
  WPC e @ (S k); ⊤ {{ Φ }} {{ Φc }}.
Proof using stagedG0.
  iIntros "(His_foo&Hfupd)".
  rewrite bi.and_comm.
  rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
  iDestruct (own_discrete_elim_conj with "Hfupd") as (Q_keep Q_inv) "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
  iMod (pending_alloc) as (γpending) "Hpending".
  iMod (inv_mut_alloc (S k) N2 _ mysch ([ Φc; staged_done γpending; C; staged_pending (3/4)%Qp γpending])%I [Q_inv] with "[HQ_inv]") as "(#Hinv&Hfull)".
  { rewrite mysch_interp_strong. iLeft. iSplit; first auto.
    iMod ("Hwand1" with "[$]") as "H".
    iModIntro. iMod (fupd_level_split_level with "H") as "$".
    { lia. }
    eauto.
  }
  iDestruct (pending_split34 with "Hpending") as "(Hpend34&Hpend14)".
  (*
  iAssert (<disc> |C={⊤}_(S k)=> Φc)%I with "[Hpend34]" as "Hcfupd".
  {
    iModIntro. iIntros "HC".
    iMod (inv_mut_acc with "Hinv") as (Qs) "(H&Hclo)"; first auto.
    rewrite mysch_interp_weak /=.
    iDestruct "H" as "[(_&>H)|[Hfalse1|Hfalse2]]".
    * iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def).
      iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
      iMod (fupd_split_level_le with "H") as "H"; first lia.
      iMod "Hclo''".
      iSpecialize ("Hclo" with "[HC Hpend34]").
      { iRight. iLeft. iFrame. }
      iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def) in "Hclo".
      iMod "Hclo". eauto.
    * iDestruct "Hfalse1" as "(>_&>?)". iDestruct (pending34_pending34 with "[$] [$]") as "[]".
    * iDestruct "Hfalse2" as ">?". iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iMod "Hcfupd".
   *)
  iAssert (WPC e @ S k; ⊤ {{ v, staged_pending (3 / 4)%Qp γpending -∗ |NC={⊤}=> Φ v }} {{ True }})%I with "[His_foo HQ_keep Hpend14 Hfull]" as "Hwpc";
    last first.
  {
    iApply wpc_ncfupd.
    iApply (wpc_strong_mono with "Hwpc"); auto.
    iSplit.
    * iIntros (?) "Hwand". iModIntro. iApply "Hwand". by iFrame.
    * iIntros "_ HC".
      {
        iMod (inv_mut_acc with "Hinv") as (Qs) "(H&Hclo)"; first auto.
        rewrite mysch_interp_weak /=.
        iDestruct "H" as "[(_&>H)|[Hfalse1|Hfalse2]]".
        * iApply (fupd_level_fupd _ _ _ (S k)).
          iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def).
          iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
          iMod (fupd_split_level_le with "H") as "H"; first lia.
          iMod "Hclo''".
          iSpecialize ("Hclo" with "[HC Hpend34]").
          { iRight. iLeft. iFrame. }
          iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def) in "Hclo".
          iMod "Hclo". by iDestruct "H" as ">$".
        * iDestruct "Hfalse1" as "(>_&>?)". iDestruct (pending34_pending34 with "[$] [$]") as "[]".
        * iDestruct "Hfalse2" as ">?". iDestruct (pending_done with "[$] [$]") as "[]".
      }
  }
  iApply (wp_wpc).
  iApply wp_ncfupd.
  wp_apply (wp_spec). iFrame "His_foo".
  iIntros (σ) "HP".
  rewrite ncfupd_eq /ncfupd_def. iIntros (q) "HNC".
  iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
  { solve_ndisj. }
  rewrite ?mysch_interp_strong.
  iDestruct "H" as "[HQ|Hfalse]"; last first.
  { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
    * iDestruct (NC_C with "[$] [$]") as "[]".
    * iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iDestruct "HQ" as "(HQ&_)".
  iMod ("Hwand2" with "[$]") as "Hfupd".
  iLeft in "Hfupd".
  iMod fupd_mask_subseteq as "HcloseM"; last iMod ("Hfupd" with "[$] [$]") as "((HP&HΦ)&HNC)"; first by solve_ndisj.
  iMod "HcloseM".
  iEval (rewrite bi.and_comm) in "HΦ".
  iClear "Hwand1 Hwand2".
  iDestruct (own_discrete_elim_conj with "HΦ") as (Q_keep' Q_inv') "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
  iMod ("Hclo" $! [Q_inv'] with "[HQ_inv]") as "Hfull".
  { rewrite ?mysch_interp_strong. iLeft. iSplit; first auto.
    iMod ("Hwand1" with "[$]") as "H".
    iModIntro. iMod (fupd_level_split_level with "H") as "$".
    { lia. }
    eauto.
  }
  iModIntro. iFrame "HP". iFrame.
  iIntros (q0) "HNC". iModIntro. iFrame.
  iIntros "Hpend34" (q1) "HNC".
  iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
  rewrite ?mysch_interp_strong.
  iDestruct "H" as "[HQ|Hfalse]"; last first.
  { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
    * iDestruct (NC_C with "[$] [$]") as "[]".
    * iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iDestruct "HQ" as "(HQ&_)".
  iMod ("Hwand2" with "[$]") as "(HΦ&_)".
  iDestruct (pending_join34 with "[$]") as "Hpend".
  iMod (pending_upd_done with "Hpend") as "Hdone".
  iMod ("Hclo" $! [True]%I with "[Hdone]").
  { rewrite ?mysch_interp_strong. iRight. by iRight. }
  iFrame. eauto.
Qed.

End wpc_spec.

End goose.
