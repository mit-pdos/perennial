From iris.algebra Require Import auth gmap.
Require Export CSL.Refinement.
Require Import StatDb.Impl StatDb.WeakestPre.
Set Default Proof Using "Type".



Section refinement_triples.
  Context `{!varG Σ, !lockG Σ, !@cfgG (DB.Op) (DB.l) Σ}.
  Context (ρ : thread_pool DB.Op * DB.l.(State)).

  Import Var.

  Definition DBLockInv :=
    (∃ l, source_state l ∗ Sum ↦ (fold_right plus O l) ∗ Count ↦ (length l))%I.

  Definition DBInv := (source_ctx ρ ∗ ∃ N γ, is_lock N γ DBLockInv)%I.

  (* TODO: write smart tactics for applying the wp_primitives *)
  Lemma add_refinement {T} j (K: unit → proc DB.Op T) n:
    {{{ j ⤇ Bind (Call (DB.Add n)) K ∗ DBInv }}} add n {{{ RET tt; j ⤇ Bind (Ret tt) K }}}.
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
    iMod (ghost_step_lifting_bind with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { set_solver+. }
    iAssert DBLockInv with "[-HΦ Hlocked Hj]" as "HDB".
    { iExists _; iFrame. }
    iApply (wp_unlock with "[-HΦ Hj]"); iFrame.
    { iFrame "Hinv"; eauto. }
    iIntros "!> _". by iApply "HΦ".
  Qed.

  Lemma avg_refinement {T} j (K: nat → proc DB.Op T):
    {{{ j ⤇ Bind (Call (DB.Avg)) K ∗ DBInv }}} avg {{{ n, RET n; j ⤇ Bind (Ret n) K }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (N γ) "#Hinv".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HDB)".
    iDestruct "HDB" as (l) "(Hsource&Hsum&Hcount)".
    wp_bind. iApply (wp_read with "Hsum"). iIntros "!> Hsum".
    wp_bind. iApply (wp_read with "Hcount"). iIntros "!> Hcount".
    iMod (ghost_step_lifting_bind with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { set_solver+. }
    iAssert DBLockInv with "[-HΦ Hlocked Hj]" as "HDB".
    { iExists _; iFrame. }
    wp_bind. iApply (wp_unlock with "[-HΦ Hj]"); iFrame.
    { iFrame "Hinv"; eauto. }
    iIntros "!> _".
    wp_ret. by iApply "HΦ".
  Qed.
End refinement_triples.