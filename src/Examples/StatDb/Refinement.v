From iris.algebra Require Import auth gmap.
Require Export CSL.Refinement.
Require Import StatDb.Impl StatDb.WeakestPre.
Set Default Proof Using "Type".
Unset Implicit Arguments.



Section refinement_triples.
  Context `{!varG Σ, !lockG Σ, !@cfgG (DB.Op) (DB.l) Σ}.
  Context (ρ : thread_pool DB.Op * DB.l.(State)).

  Import Var.

  Definition DBLockInv :=
    (∃ l, source_state l ∗ Sum ↦ (fold_right plus O l) ∗ Count ↦ (length l))%I.

  Definition DBInv := (source_ctx ρ ∗ ∃ N γ, is_lock N γ DBLockInv)%I.

  (* TODO: write smart tactics for applying the wp_primitives *)
  Lemma add_refinement {T} j K `{LanguageCtx DB.Op unit T DB.l K} n:
    {{{ j ⤇ K (Call (DB.Add n)) ∗ DBInv }}} add n {{{ v, RET v; j ⤇ K (Ret v) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (N γ) "#Hinv".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HDB)".
    iDestruct "HDB" as (l) "(Hsource&Hsum&Hcount)".
    wp_bind. iApply (wp_read with "Hsum"). iIntros "!> Hsum".
    wp_bind. iApply (wp_write with "[$]"). iIntros "!> Hsum".
    wp_bind. iApply (wp_read with "Hcount"). iIntros "!> Hcount".
    wp_bind. iApply (wp_write with "[$]"). iIntros "!> Hcount".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { set_solver+. }
    iAssert DBLockInv with "[-HΦ Hlocked Hj]" as "HDB".
    { iExists _; iFrame. }
    iApply (wp_unlock with "[-HΦ Hj]"); iFrame.
    { iFrame "Hinv"; eauto. }
    iIntros "!> _". by iApply "HΦ".
  Qed.

  Lemma avg_refinement {T} j K `{LanguageCtx DB.Op nat T DB.l K}:
    {{{ j ⤇ K (Call (DB.Avg)) ∗ DBInv }}} avg {{{ n, RET n; j ⤇ K (Ret n) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (N γ) "#Hinv".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HDB)".
    iDestruct "HDB" as (l) "(Hsource&Hsum&Hcount)".
    wp_bind. iApply (wp_read with "Hsum"). iIntros "!> Hsum".
    wp_bind. iApply (wp_read with "Hcount"). iIntros "!> Hcount".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { set_solver+. }
    iAssert DBLockInv with "[-HΦ Hlocked Hj]" as "HDB".
    { iExists _; iFrame. }
    wp_bind. iApply (wp_unlock with "[-HΦ Hj]"); iFrame.
    { iFrame "Hinv"; eauto. }
    iIntros "!> _".
    wp_ret. by iApply "HΦ".
  Qed.

  (* TODO: stop 'compile' from getting unfolded by the various Iris tactics. *)

  (* TODO: this induction argument is completely generic; so should be bundled
     for arbitrary layers.  The important points are to show triples for each
     prim op compilation with some common invariant (here, DBInv) which must
     be Persistent and must imply source_ctx for some ρ. *)
  Lemma induction_refinement {T1 T2} j K `{LanguageCtx DB.Op T1 T2 DB.l K} (e: proc DB.Op T1):
    j ⤇ K e ∗ DBInv ⊢ WP StatDb.Impl.impl.(compile) e {{ v, j ⤇ K (Ret v) }}.
  Proof.
    iIntros "(Hj&#Hinv)".
    iInduction e as [] "IH" forall (j T2 K H0).
    - destruct op.
      * iApply (add_refinement j K with "[$]"); eauto.
      * iApply (avg_refinement j K with "[$]"); eauto.
    - wp_ret. eauto.
    - wp_bind.
      iApply wp_wand_l. iSplitL ""; last first.
      * iApply ("IH1" $! _ _ (fun x => K (Bind x p2)) with "[] Hj"); try iFrame.
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (?) "Hj".
        iMod (ghost_step_bind_ret with "Hj []") as "Hj".
        { set_solver+. }
        { iDestruct "Hinv" as "($&?)". }
        iApply "IH"; auto.
    - iLöb as "IHloop" forall (init).
      iMod (ghost_step_loop with "Hj []") as "Hj".
      { set_solver+. }
      { iDestruct "Hinv" as "($&?)". }
      wp_loop.
      iApply wp_wand_l.
      iSplitL ""; last first.
      * rewrite /loop1. simpl.
        iApply ("IH" $! _ _ _ (fun x => K (Bind x
                               (fun out => match out with
                               | ContinueOutcome x => Loop body x
                               | DoneWithOutcome r => Ret r
                               end))) with "[] Hj")%proc.
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (out) "Hj".
        destruct out.
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { iDestruct "Hinv" as "($&?)". }
             by iApply "IHloop".
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { iDestruct "Hinv" as "($&?)". }
           by wp_ret.
   - iMod (ghost_step_spawn with "Hj []") as "(Hj&Hj')".
     { set_solver+. }
     { iDestruct "Hinv" as "($&?)". }
     iDestruct "Hj'" as (j') "Hj'".
     iApply (wp_spawn with "[Hj'] [Hj]").
     { iNext. iApply wp_wand_l; iSplitL ""; last first.
       { iApply ("IH" $! _ _ (fun x => x)); first (iPureIntro; apply _).
         iFrame. }
       eauto. }
     eauto.
  Qed.

End refinement_triples.