From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers coPset gset.
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

Record lockservice_names := LockserviceGN {
  ls_rpcGN : rpc_names;
  ls_locksAllocGN : gname;
  ls_locksMapDomGN : gname;
}.

Class lockserviceG Σ := LockserviceG {
  ls_rpcG :> rpcG Σ u64; (* RPC layer ghost state *)
  ls_locksAllocG :> mapG Σ u64 bool; (* [ls_locksAllocGN]: tracks with locks *logically* exist; true=exists *)
  ls_locksMapDomG :> ghost_varG Σ (gset u64); (* [ls_mapDomGN]: Tracking the set of locks that *physically* exist *)
}.

Definition lockserviceN := nroot .@ "lockservice".
Definition lockserviceInvN := nroot .@ "lockservice" .@ "inv".
Definition locknameN (lockname : u64) := lockserviceN .@ "lock" .@ lockname.

Section lockservice_proof.
Context `{!heapG Σ, !lockserviceG Σ}.
Context {Ps : u64 -> iProp Σ}. (* Per-lock invariant *)

Implicit Types (γ : lockservice_names).

(** A token for being allowed to allocate a lock name. *)
Definition lockservice_alloc_token γ (ln:u64) : iProp Σ :=
  ln [[ γ.(ls_locksAllocGN) ]]↦ false.

(** Witness showing that this lock exists *)
Definition lockservice_is_lock γ (ln:u64) : iProp Σ :=
  ln [[ γ.(ls_locksAllocGN) ]]↦ro true.

Definition TryLock_Post : u64 -> u64 -> iProp Σ := λ args reply, (⌜reply = 0⌝ ∨ ⌜reply = 1⌝ ∗ (Ps args))%I.
Definition TryLock_Pre γ : u64 -> iProp Σ := (λ args, lockservice_is_lock γ args)%I.

Definition Unlock_Post : u64 -> u64 -> iProp Σ := λ args reply, True %I.
Definition Unlock_Pre γ : u64 -> iProp Σ := (λ args, lockservice_is_lock γ args ∗ (Ps args))%I.

(** Lockserver invariant (maintained even when the Mutex is held) *)
Definition Lockserver_inv γ : iProp Σ :=
  ∃ (locksAlloc: gmap u64 bool) (locksMapDom:gset u64),
    "Hdom" ∷ ghost_var γ.(ls_locksMapDomGN) (1/2) locksMapDom ∗ (* we know the lock domain *)
    "Hlocks" ∷ map_ctx γ.(ls_locksAllocGN) 1 locksAlloc ∗ (* we own the logical lock tracking *)
    "HlocksEx" ∷ ⌜locksMapDom ⊆ dom (gset _) locksAlloc⌝ ∗ (* all physically-existing locks exist logically *)
    "HlocksNew" ∷ [∗ map] ln ↦ ex ∈ locksAlloc,
      (* all logically-existing locks either exist physically or have their invariant here *)
      (⌜ex = false ∨ ln ∈ locksMapDom⌝ ∨ Ps ln)
.

(** Lockserver mutex invariant *)
Definition LockServer_own_core γ (srv:loc) : iProp Σ :=
  ∃ (locks_ptr:loc) (locksM:gmap u64 bool),
    "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr ∗ (* we own the "locks" field *)
    "Hmap" ∷ is_map (locks_ptr) locksM ∗ (* we control the physical map *)
    "HmapDom" ∷ ghost_var γ.(ls_locksMapDomGN) (1/2) (dom (gset _) locksM) ∗ (* the physical domain ghost variable matches the physical map *)
    "Hlockeds" ∷ [∗ map] ln ↦ locked ∈ locksM, (⌜locked=true⌝ ∨ (Ps ln)) (* we own the invariants of all not-held locks *)
.

Definition is_lockserver (srv:loc) γ : iProp Σ :=
  "#Hinv" ∷ inv lockserviceInvN (Lockserver_inv γ) ∗
  "#Hmutex" ∷ is_server (Server_own_core:=LockServer_own_core γ) srv γ.(ls_rpcGN).

(** Allocate a new lock in the lockservice, given the corresponding token
and the lock invariant. *)
Lemma lockservice_alloc_lock γ (srv:loc) ln E :
  ↑lockserviceN ⊆ E →
  is_lockserver srv γ -∗
  Ps ln -∗
  lockservice_alloc_token γ ln ={E}=∗ lockservice_is_lock γ ln.
Proof.
  iIntros (?) "Hserver HP Htok". iNamed "Hserver".
  iInv "Hinv" as "Hlockinv".
  (* FIXME: looks like iNamed does not handle the ▷ here *)
  iDestruct "Hlockinv" as (locksAlloc locksMapDom) "(>Hdom & >Hlocks & >HlocksEx & HlocksNew)".
  iDestruct (map_valid with "Hlocks Htok") as %Hlookup.
  iMod (map_update ln false true with "Hlocks Htok") as "[Hlocks Htok]".
  iMod (map_freeze with "Hlocks Htok") as "[Hlocks $]".
  iModIntro. iSplitL; last done. iNext.
  iExists _, locksMapDom. iFrame. iSplit.
  - iDestruct "HlocksEx" as %HlocksEx. iPureIntro. set_solver.
  - iApply (big_sepM_insert_override_2 with "HlocksNew"); first done.
    iIntros "_". eauto.
Qed.

Lemma tryLock_core_spec γ (srv:loc) (ln:u64) :
inv lockserviceInvN (Lockserver_inv γ) -∗
{{{ 
     LockServer_own_core γ srv ∗ TryLock_Pre γ ln
}}}
  LockServer__tryLock_core #srv #ln
{{{
   v, RET v; LockServer_own_core γ srv
      ∗ (∃b:u64, ⌜v = #b⌝ ∗ TryLock_Post ln b)
}}}.
Proof.
  iIntros "#Hinv" (Φ) "!# [Hlsown #Hpre] Hpost".
  wp_lam.
  wp_let.
  iNamed "Hlsown".
  wp_loadField.
  wp_apply (wp_MapGet with "Hmap"); eauto.
  iIntros (locked ok) "[% HlocksMap]".
  rewrite /TryLock_Pre.
  wp_pures.
  destruct locked.
  - (* Lock already held by someone *)
    wp_pures.
    iApply "Hpost".
    iSplitR "".
    { iExists _, _; iFrame. }
    iExists _. iSplit; eauto; last by iLeft.
  - wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlocksMap"); first eauto; iIntros "HlocksMap".
    destruct ok.
    + (* Lock already existed. *)
      apply map_get_true in H.
      iDestruct (big_sepM_insert_acc with "Hlockeds") as "[HP Hlockeds]"; first done.
      iDestruct "HP" as "[%|HP]"; first done.
      iSpecialize ("Hlockeds" $! true with "[]"); first by eauto.
      
      wp_pures. iApply "Hpost".

      rewrite /TryLock_Post.
      iSplitR "HP"; last by eauto with iFrame.

      iExists _, _; iFrame.
      replace (dom (gset u64) (<[ln:=true]> locksM)) with (dom (gset u64) locksM); first done.
      rewrite dom_insert_L.
      assert (ln ∈ dom (gset u64) locksM).
      { apply elem_of_dom. eauto. }
      set_solver.
    + (* The lock did not exist yet, we have to "physically allocate" it. *)
      apply map_get_false in H as [H _].
      iApply fupd_wp.
      iInv "Hinv" as (locksAlloc locksDom) "(>Hdom & >Hlocks & >HlocksEx & HlocksNew)".
      iDestruct (ghost_var_agree with "HmapDom Hdom") as %<-.
      iMod (ghost_var_update_halves ({[ ln ]} ∪ dom (gset _) locksM) with "HmapDom Hdom") as "[HmapDom Hdom]".
      iDestruct (map_valid with "Hlocks Hpre") as %Halloc.
      iDestruct (big_sepM_delete with "HlocksNew") as "[HP HlocksNew]"; first exact Halloc.
      iDestruct "HP" as "[>HP|HP]".
      { iDestruct "HP" as %[HP|HP%elem_of_dom]; first done. exfalso.
        destruct HP as [? HP]. rewrite HP in H. done. }
      iModIntro. iSplitL "HlocksNew HlocksEx Hlocks Hdom".
      { iNext. iExists _, _. iFrame "Hdom Hlocks".
        iSplit.
        - iDestruct "HlocksEx" as %HlocksEx. iPureIntro.
          assert (ln ∈ dom (gset _) locksAlloc). { apply elem_of_dom. eauto. }
          set_solver.
        - iApply (big_sepM_delete _ _ ln); first done. iSplitR.
          { iLeft. iPureIntro. right. set_solver. }
          iApply (big_sepM_mono with "HlocksNew").
          intros ln' ? _. simpl. iIntros "[Hln'|Hln']"; last by eauto.
          iLeft. iDestruct "Hln'" as %[?|Hln']; first by eauto.
          iPureIntro. right. set_solver. }
      iModIntro. wp_pures. iApply "Hpost".

      rewrite /TryLock_Post.
      iSplitR "HP"; last by eauto with iFrame.
      iExists _, _. iFrame.
      rewrite /typed_map.map_insert dom_insert_L. iFrame "HmapDom".
      iApply big_sepM_insert; first done. iFrame "Hlockeds". eauto.
Qed.

Lemma unlock_core_spec γ (srv:loc) (ln:u64) :
{{{
     LockServer_own_core γ srv ∗ Unlock_Pre γ ln
}}}
  LockServer__unlock_core #srv #ln
{{{
   v, RET v; LockServer_own_core γ srv
      ∗ (∃b:u64, ⌜v = #b⌝ ∗ Unlock_Post ln b)
}}}.
Proof.
  iIntros (Φ) "[Hlsown Hpre] Hpost".
  wp_lam.
  wp_let.
  iNamed "Hlsown".
  wp_loadField.
  wp_apply (wp_MapGet with "Hmap"); eauto.
  iIntros (locked ok) "[% HlocksMap]".
  destruct locked.
  - (* Locks was previously held. *)
    destruct ok; last first.
    { (* Not already in domain? Impossible. *)
      apply map_get_false in H as [_ H]. done. }
    apply map_get_true in H.
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlocksMap"); eauto; iIntros "HlocksMap".
    iDestruct "Hpre" as "[#Hpre HP]".
    iDestruct (big_sepM_insert_acc with "Hlockeds") as "[_ Hlockeds]"; first done.
    iSpecialize ("Hlockeds" $! false with "[HP]").
    { eauto. }

    wp_pures. iApply "Hpost".
    iSplit; last by eauto.
    iExists _, _; iFrame.
    replace (dom (gset u64) (<[ln:=false]> locksM)) with (dom (gset u64) locksM); first done.
    rewrite dom_insert_L.
    assert (ln ∈ dom (gset u64) locksM).
    { apply elem_of_dom. eauto. }
    set_solver.
  - wp_pures. iApply "Hpost". iSplitL; eauto.
    iExists _, _; iFrame.
Qed.

Lemma Clerk__TryLock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    own_clerk ck srv γ.(ls_rpcGN) ∗
    is_lockserver srv γ 
  }}}
    Clerk__TryLock ck #ln
  {{{ v, RET v; ∃(b:u64), ⌜v = #b⌝ ∗ own_clerk ck srv γ.(ls_rpcGN) ∗ (⌜b = 0⌝ ∨ ⌜b = 1⌝ ∗ Ps ln) }}}.
Proof using Type*.
  iIntros (Φ) "(#Htok & Hclerk & #[Hinv Hserver]) Hpost".
  iApply (Clerk__from_core LockServer__tryLock_core "LockServer__TryLock" "CallTryLock" "Clerk__TryLock" _ _ _ _ (TryLock_Pre γ) TryLock_Post with "[] [Hclerk]").
  - by unfold name_neq.
  - iIntros "* % !# [??]". iApply tryLock_core_spec; eauto.
  - eauto with iFrame.
  - eauto.
Qed.

Lemma Clerk__Unlock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    Ps ln ∗
    own_clerk ck srv γ.(ls_rpcGN) ∗
    is_lockserver srv γ 
  }}}
    Clerk__Unlock ck #ln
    {{{ v, RET v; ∃(b:u64), ⌜v = #b⌝ ∗ own_clerk ck srv γ.(ls_rpcGN) ∗ True }}}.
Proof using Type*.
  iIntros (Φ) "(#Htok & HP & Hclerk & #[Hinv Hserver]) Hpost".
  iApply (Clerk__from_core LockServer__unlock_core "LockServer__Unlock" "CallUnlock" "Clerk__Unlock" _ _ _ _ (Unlock_Pre γ) Unlock_Post with "[] [Hclerk HP]").
  - by unfold name_neq.
  - iIntros "* % !#". iApply unlock_core_spec.
  - eauto with iFrame.
  - eauto.
Qed.

Lemma Clerk__Lock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    own_clerk ck srv γ.(ls_rpcGN) ∗
    is_lockserver srv γ
  }}}
    Clerk__Lock ck #ln
  {{{ RET #true; own_clerk ck srv γ.(ls_rpcGN) ∗ Ps ln }}}.
Proof using Type*.
  iIntros (Φ) "[#Htok [Hclerk_own #Hinv]] Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_forBreak
              (fun c =>
                 (own_clerk ck srv _ ∗ Ps ln -∗ Φ #true)
                 ∗ own_clerk ck srv _
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
