From iris.algebra Require Export auth functions csum.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting.
Require Import Helpers.RelationTheorems.
From iris.proofmode Require Export tactics.
From RecoveryRefinement Require Export Lib.

Class tregG Σ := TRegG {
                     treg_counter_inG :> inG Σ (csumR countingR (authR (optionUR (exclR unitC))));
                     treg_name: gname
                   }.
Arguments treg_name {_}.

Section thread_reg.
  Context `{tr: tregG Σ}.
  Definition Registered :=
    own (treg_name tr) (Cinl (Count (-1)%Z)).
  Definition AllDone :=
    own (treg_name tr) (Cinr (◯ (Excl' tt))).
  Lemma AllDone_Register_excl:
    AllDone -∗ Registered -∗ False.
  Proof. iIntros "Had Hreg". iDestruct (own_valid_2 with "Had Hreg") as %[]. Qed.
End thread_reg.


Definition thread_count_interp {Σ} {tr: tregG Σ} :=
  λ n, (match n with
         | 1 => own (treg_name tr) (Cinl (Count 1)) ∨ own (treg_name tr) (Cinr (● (Excl' tt)))
         | _ => own (treg_name tr) (Cinl (Count n))
         end)%I.

Module Reg_wp.
Section Reg_wp.
Context {OpT} {Λ: Layer OpT} `{IRIS: irisG OpT Λ Σ}.
Context `{!tregG Σ}.

Lemma fst_lift_puts_inv {A B} f (n1: A) (σ1 : B) n2 σ2 t :
  fst_lift (puts f) (n1, σ1) (Val (n2, σ2) t) →
  n2 = f n1 ∧
  σ2 = σ1 ∧
  t = tt.
Proof.
  intros [Hput ?].
  inversion Hput; subst; auto.
Qed.

Context (Interp: OpState Λ → iProp Σ).
Context (Hinterp1: ∀ n σ, state_interp (n, σ) -∗ thread_count_interp n ∗ Interp σ).
Context (Hinterp2: ∀ n σ, thread_count_interp n ∗ Interp σ -∗ state_interp (n, σ)).

Lemma wp_spawn {T} s E (e: proc _ T) Φ :
  ▷ Registered
    -∗ ▷ (Registered -∗ WP (let! _ <- e; Unregister)%proc @ s; ⊤ {{ _, True }})
    -∗ ▷ ( Registered -∗ Φ tt)
    -∗ WP Spawn e @ s; E {{ Φ }}.
Proof.
  iIntros "Hreg He HΦ".
  iApply wp_lift_atomic_step.
  { auto. }
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; intuition. iPureIntro. eapply spawn_non_errorable. }
  iIntros (e2 (n', σ2) ? Hstep) "!>".
  destruct Hstep as ([]&(?&?)&Hput&Hpure).
  inversion Hpure. subst.
  apply fst_lift_puts_inv in Hput as (?&?&?); subst.

  iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
  iAssert (own (treg_name _) (Cinl (Count n)) ∗ Registered)%I
          with "[Hown Hreg]" as "(Hown&Hreg)".
  {
    destruct (decide (n = 1)) as [->|]; last first.
    {  destruct n as [|[|n]]; try lia; iFrame. }
    iDestruct "Hown" as "[Hown|Hown]"; first by iFrame.
    iDestruct (own_valid_2 with "Hown Hreg") as %[].
  }
  iAssert (own (treg_name _) (Cinl (Count (S n))) ∗ Registered)%I
          with "[Hown]" as "(Hown&Hreg')".
  {
    rewrite -own_op Cinl_op counting_op' //=.
    repeat destruct decide; try lia. replace (S n + (-1))%Z with (n : Z) by lia. done.
  }
  iModIntro. simpl. iFrame.
  iSplitL "Hown Hrest".
  { iApply Hinterp2. destruct n; iFrame. }
  iSplitL "Hreg HΦ".
  { by iApply "HΦ". }
  rewrite right_id.
  by iApply "He".
Qed.

Lemma wp_unregister s E :
  {{{ ▷ Registered }}} Unregister @ s; E {{{ RET tt; True }}}.
Proof.
  iIntros (Φ) ">Hreg HΦ".
  iApply wp_lift_atomic_step.
  { auto. }
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; intuition. iPureIntro. eapply unregister_non_errorable. }
  iIntros (e2 (n', σ2) ? Hstep) "!>".
  destruct Hstep as ([]&(?&?)&Hput&Hpure).
  inversion Hpure. subst.
  apply fst_lift_puts_inv in Hput as (?&?&?); subst.
  iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".

  iAssert (∃ n', ⌜ n = S n' ⌝ ∗ own (treg_name _) (Cinl (Count n)) ∗ Registered)%I
          with "[Hown Hreg]" as (n' Heq) "(Hown&Hreg)".
  {
    destruct (decide (n = 1)) as [->|]; last first.
    {  destruct n as [|[|n]]; try lia.
       - iDestruct (own_valid_2 with "Hown Hreg") as %[].
       - iExists (S n). iFrame; eauto.
    }
    iExists O. iDestruct "Hown" as "[Hown|Hown]"; first by (iFrame).
    iDestruct (own_valid_2 with "Hown Hreg") as %[].
  }
  subst.
  iAssert (own (treg_name _) (Cinl (Count n')))%I
          with "[Hown Hreg]" as "Hown".
  {
    iCombine "Hown Hreg" as "Hown".
    rewrite Cinl_op counting_op' //=.
    repeat destruct decide; try lia. replace (S n' + (-1))%Z with (n' : Z) by lia. done.
  }
  iModIntro. simpl. iFrame. iSplitL "Hown Hrest".
  { iApply Hinterp2. destruct n' as [|[|n']]; iFrame. }
  rewrite right_id.
  by iApply "HΦ".
Qed.

Lemma wp_wait s E :
  {{{ ▷ Registered }}} Wait @ s; E {{{ RET tt; AllDone }}}.
Proof.
  iIntros (Φ) ">Hreg HΦ".
  iApply wp_lift_atomic_step.
  { auto. }
  iIntros ((n, σ)) "Hown".
  iModIntro. iSplit.
  { destruct s; intuition. iPureIntro. eapply wait_non_errorable. }
  iIntros (e2 (n', σ2) ? Hstep) "!>".
  destruct Hstep as ([]&(?&?)&Hput&Hpure).
  inversion Hpure. subst.
  inversion Hput as [Hsuch Heq]. subst.
  inversion Hsuch; subst.
  iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".

  iAssert (own (treg_name _) (Cinl (Count 1)) ∗ Registered)%I
          with "[Hown Hreg]" as "(Hown&Hreg)".
  {
    iDestruct "Hown" as "[Hown|Hown]"; first by (iFrame).
    iDestruct (own_valid_2 with "Hown Hreg") as %[].
  }
  subst.
  iAssert (own (treg_name _) (Cinl (Count O)))%I
          with "[Hown Hreg]" as "Hown".
  {
    iCombine "Hown Hreg" as "Hown".
    rewrite Cinl_op counting_op' //=.
  }
  iMod (own_update with "Hown") as "(Hdone&Hown)".
  { apply cmra_update_exclusive with (y:=Cinr (◯ (Excl' tt)) ⋅ Cinr (● (Excl' tt))) => //=. }
  iModIntro.
  iSplitL "Hown Hrest".
  { iApply Hinterp2; iFrame. }
  simpl.
  rewrite right_id.
  by iApply "HΦ".
Qed.

End Reg_wp.
End Reg_wp.