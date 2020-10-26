From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map fmcounter.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map rpc common_proof nondet.

Section lockservice_proof.
Context `{!heapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition locknameN (lockname : u64) := nroot .@ "lock" .@ lockname.

  Context `{!rpcG Σ u64}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{Ps : u64 -> iProp Σ}.

  Parameter validLocknames : gmap u64 unit.


Definition TryLock_Post : u64 -> u64 -> iProp Σ := λ args reply, (⌜reply = 0⌝ ∨ ⌜reply = 1⌝ ∗ (Ps args))%I.
Definition TryLock_Pre : u64 -> iProp Σ := λ args, ⌜is_Some (validLocknames !! args)⌝%I.

Definition Unlock_Post : u64 -> u64 -> iProp Σ := λ args reply, True %I.
Definition Unlock_Pre : u64 -> iProp Σ := λ args, (⌜is_Some (validLocknames !! args)⌝ ∗ (Ps args))%I.

Definition LockServer_own_core (srv:loc) : iProp Σ :=
  ∃ (locks_ptr:loc) (locksM:gmap u64 bool),
  "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr
∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
∗ "HlocksMap" ∷ is_map (locks_ptr) locksM
.

Definition is_lockserver := is_server (Server_own_core:=LockServer_own_core).

Lemma tryLock_core_spec (srv:loc) (tryLockArgs:u64) :
{{{ 
     LockServer_own_core srv ∗ TryLock_Pre tryLockArgs
}}}
  LockServer__tryLock_core #srv #tryLockArgs
{{{
   v, RET v; LockServer_own_core srv
      ∗ (∃b:u64, ⌜v = #b⌝ ∗ TryLock_Post tryLockArgs b)
}}}.
Proof.
  iIntros (Φ) "[Hlsown Hpre] Hpost".
  wp_lam.
  wp_let.
  iNamed "Hlsown".
  wp_loadField.
  wp_apply (wp_MapGet with "HlocksMap"); eauto.
  iIntros (locked ok) "[% HlocksMap]".
  iDestruct "Hpre" as %Hpre.
  destruct locked.
  + (* Lock already held by someone *)
    wp_pures.
    iApply "Hpost".
    iSplitR "".
    { iExists _, _; iFrame. }
    iExists _. iSplit; eauto; last by iLeft.
  + wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlocksMap"); first eauto; iIntros "HlocksMap".
    iDestruct (big_sepM2_dom with "Hlockeds") as %HlocksDom.
    iDestruct (big_sepM2_delete _ _ _ tryLockArgs false () with "Hlockeds") as "[HP Hlockeds]".
    {
      rewrite /map_get in H.
      assert (is_Some (locksM !! tryLockArgs)) as HLocknameInLocks.
      { apply elem_of_dom. apply elem_of_dom in Hpre. rewrite HlocksDom. done. }
      destruct HLocknameInLocks as [ x  HLocknameInLocks].
      rewrite HLocknameInLocks in H.
        by injection H as ->.
    }
    { by destruct Hpre as [ [] HLocknameValid]. }
    iDestruct (big_sepM2_insert_delete _ _ _ tryLockArgs true () with "[$Hlockeds]") as "Hlockeds"; eauto.
    iDestruct "HP" as "[%|HP]"; first discriminate.
    wp_pures. iApply "Hpost".

    replace (<[tryLockArgs:=()]> validLocknames) with (validLocknames).
    2:{ rewrite insert_id; eauto. by destruct Hpre as [ [] HLocknameValid]. }

    iSplitR "HP".
    { iExists _, _; iFrame. }
    iExists _; iSplit; eauto.
    iRight. by iFrame.
Qed.

Lemma unlock_core_spec (srv:loc) (unLockArgs:u64) :
{{{
     LockServer_own_core srv ∗ Unlock_Pre unLockArgs
}}}
  LockServer__unlock_core #srv #unLockArgs
{{{
   v, RET v; LockServer_own_core srv
      ∗ (∃b:u64, ⌜v = #b⌝ ∗ Unlock_Post unLockArgs b)
}}}.
Proof.
  iIntros (Φ) "[Hlsown Hpre] Hpost".
  wp_lam.
  wp_let.
  iNamed "Hlsown".
  wp_loadField.
  wp_apply (wp_MapGet with "HlocksMap"); eauto.
  iIntros (locked ok) "[% HlocksMap]".
  destruct locked.
  {
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlocksMap"); eauto; iIntros "HlocksMap".
    iDestruct "Hpre" as (Hpre) "HP".
    iDestruct (big_sepM2_dom with "Hlockeds") as %HlocksDom.
    iDestruct (big_sepM2_delete _ _ _ unLockArgs true () with "Hlockeds") as "[H_ Hlockeds]"; eauto.
    {
      rewrite /map_get in H.
      assert (is_Some (locksM !! unLockArgs)) as HLocknameInLocks.
      { apply elem_of_dom. apply elem_of_dom in Hpre. rewrite HlocksDom. done. }
      destruct HLocknameInLocks as [ x  HLocknameInLocks].
      rewrite HLocknameInLocks in H.
        by injection H as ->.
    }
    { by destruct Hpre as [ [] Hpre]. }
    iDestruct (big_sepM2_insert_delete _ _ _ unLockArgs false () with "[$Hlockeds $HP]") as "Hlockeds"; eauto.
    replace (<[unLockArgs:=()]> validLocknames) with (validLocknames).
    2:{ rewrite insert_id; eauto. by destruct Hpre as [ [] HLocknameValid]. }
    wp_seq.
    iApply "Hpost".
    iSplit; eauto.
    iExists _, _; iFrame.
  }
  {
    wp_pures. iApply "Hpost". iSplitL; eauto.
    iExists _, _; iFrame.
  }
Qed.

Lemma Clerk__TryLock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc 
  }}}
    Clerk__TryLock ck #ln
    {{{ v, RET v; ∃(b:u64), ⌜v = #b⌝ ∗ own_clerk ck srv γrpc ∗ (⌜b = 0⌝ ∨ ⌜b = 1⌝ ∗ Ps ln) }}}.
Proof using Type*.
  iIntros (Φ) "Hpre Hpost".
  iApply (Clerk__from_core LockServer__tryLock_core "LockServer__TryLock" "CallTryLock" "Clerk__TryLock" with "[] [Hpre]").
  - by unfold name_neq.
  - iIntros "* % !#". iApply tryLock_core_spec.
  - eauto.
  - eauto.
Qed.

Lemma Clerk__Unlock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       (⌜is_Some (validLocknames !! ln)⌝
      ∗ Ps ln)
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc 
  }}}
    Clerk__Unlock ck #ln
    {{{ v, RET v; ∃(b:u64), ⌜v = #b⌝ ∗ own_clerk ck srv γrpc ∗ True }}}.
Proof using Type*.
  iIntros (Φ) "Hpre Hpost".
  iApply (Clerk__from_core LockServer__unlock_core "LockServer__Unlock" "CallUnlock" "Clerk__Unlock" with "[] [Hpre]").
  - by unfold name_neq.
  - iIntros "* % !#". iApply unlock_core_spec.
  - eauto.
  - eauto.
Qed.

Lemma Clerk__Lock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc
  }}}
    Clerk__Lock ck #ln
  {{{ RET #true; own_clerk ck srv γrpc ∗ Ps ln }}}.
Proof using Type*.
  iIntros (Φ) "[% [Hclerk_own #Hinv]] Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_forBreak
              (fun c =>
                 (own_clerk ck srv γrpc ∗ Ps ln -∗ Φ #true)
                 ∗ own_clerk ck srv γrpc
                 ∗ (⌜c = true⌝ ∨ ⌜c = false⌝∗ Ps ln)
              )%I
           with "[] [$Hclerk_own $Hpost]"); eauto.
  {
    iIntros (Ψ).
    iModIntro. iIntros "[HΦpost [Hclerk_own _]] Hpost".
    wp_apply (Clerk__TryLock_spec with "[$Hclerk_own]"); eauto.
    iIntros (tl_r) "TryLockPost".
    iDestruct "TryLockPost" as (acquired ->) "[Hown_clerk TryLockPost]".
    wp_binop.
    destruct bool_decide eqn:Hacq.
    {
      wp_pures.
      simpl.
      iApply "Hpost".
      iFrame. iRight.
      apply bool_decide_eq_true in Hacq.
      injection Hacq as Hacq.
      iDestruct "TryLockPost" as "[% | [_ HP]]"; eauto.
      { rewrite ->Hacq in *. done. }
    }
    {
      wp_pures.
      iApply "Hpost".
      iFrame. by iLeft.
    }
  }
  iIntros "(Hpost & Hown_clerk & [% | (_ & HP)])"; first discriminate.
  wp_seq.
  iApply "Hpost".
  iFrame.
Qed.

End lockservice_proof.
