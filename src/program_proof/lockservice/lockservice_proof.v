From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordUpdate.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.lockservice Require Import lockservice rpc_proof nondet.

Record lockservice_names := LockserviceNames {
  ls_rpcGN : rpc_names;
  ls_locksAllocGN : gname;
  ls_locksMapDomGN : gname;
}.

Class lockserviceG Σ := LockserviceG {
  ls_rpcG :> rpcG Σ u64; (* RPC layer ghost state *)
  ls_locksAllocG :> mapG Σ u64 unit; (* [ls_locksAllocGN]: tracks with locks *logically* exist; using 
                                        auth_map makes it convenient to have persistent facts that tell
                                        us that a lock logically exists *)
  ls_locksMapDomG :> ghost_varG Σ (gset u64); (* [ls_mapDomGN]: Tracking the set of locks that *physically* exist *)
}.

Definition lockserviceN := nroot .@ "lockservice".
Definition lockserviceInvN := nroot .@ "lockservice" .@ "inv".
Definition locknameN (lockname : u64) := lockserviceN .@ "lock" .@ lockname.

Section lockservice_proof.
Context `{!heapG Σ, !lockserviceG Σ}.
Context {Ps : u64 -> iProp Σ}. (* Per-lock invariant *)

Implicit Types (γ : lockservice_names).

(** Witness showing that this lock exists *)
Definition lockservice_is_lock γ (ln:u64) : iProp Σ :=
  ln [[ γ.(ls_locksAllocGN) ]]↦ro ().

Definition TryLock_Pre γ : RPCValC -> iProp Σ := (λ args, lockservice_is_lock γ args.1)%I.
Definition TryLock_Post : RPCValC -> u64 -> iProp Σ := λ args reply, (⌜reply = 0⌝ ∨ ⌜reply = 1⌝ ∗ (Ps args.1))%I.

Definition Unlock_Pre γ : RPCValC -> iProp Σ := (λ args, lockservice_is_lock γ args.1 ∗ (Ps args.1))%I.
Definition Unlock_Post : RPCValC -> u64 -> iProp Σ := λ args reply, True %I.

(** Lockserver invariant (maintained even when the Mutex is held) *)
Definition Lockserver_inv γ : iProp Σ :=
  ∃ (locksAlloc: gmap u64 unit) (locksMapDom:gset u64),
    "Hdom" ∷ ghost_var γ.(ls_locksMapDomGN) (1/2) locksMapDom ∗ (* we know the lock domain *)
    "Hlocks" ∷ map_ctx γ.(ls_locksAllocGN) 1 locksAlloc ∗ (* we own the logical lock tracking *)
    "HlocksEx" ∷ ⌜locksMapDom ⊆ dom (gset _) locksAlloc⌝ ∗ (* all physically-existing locks exist logically *)
    "HlocksNew" ∷ [∗ map] ln ↦ ex ∈ locksAlloc,
      (* Keep around persistent witness to lock being logically allocated for anything in the map_ctx.
         This is needed to hand out witnesses for existing locks in [lockservice_alloc_lock].
         (We can otherwise not exclude that someone somewhere fully exclusively owns this name...
         if we used the proper RA, [auth (gset u64)], instead of piggy-backing on auth_map,
         this would not be needed. *)
      ln [[γ.(ls_locksAllocGN)]]↦ro () ∗
      (* all logically-existing locks either exist physically or have their invariant here *)
      (⌜ln ∈ locksMapDom⌝ ∨ Ps ln)
.

(** Lockserver mutex invariant *)
Definition LockServer_own_core γ (srv:loc) : iProp Σ :=
  ∃ (locks_ptr:loc) (locksM:gmap u64 bool),
    "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr ∗ (* we own the "locks" field *)
    "Hmap" ∷ is_map (locks_ptr) locksM ∗ (* we control the physical map *)
    "HmapDom" ∷ ghost_var γ.(ls_locksMapDomGN) (1/2) (dom (gset _) locksM) ∗ (* the physical domain ghost variable matches the physical map *)
    "Hlockeds" ∷ [∗ map] ln ↦ locked ∈ locksM, (⌜locked=true⌝ ∨ (Ps ln)) (* we own the invariants of all not-held locks *)
.

Definition is_lockserver γ (srv:loc) : iProp Σ :=
  ∃ (sv:loc),
  "#Hinv" ∷ inv lockserviceInvN (Lockserver_inv γ) ∗
  "#Hsv" ∷ readonly (srv ↦[LockServer.S :: "sv"] #sv) ∗
  "#His_rpc" ∷ is_rpcserver sv γ.(ls_rpcGN) (LockServer_own_core γ srv).

Definition lockserver_cid_token γ cid :=
  RPCClient_own γ.(ls_rpcGN) cid 1.

Definition own_lockclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[Clerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[Clerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ls_rpcGN).

(** Allocate a new lock in the lockservice, given the prop guarded by the lock *)
Lemma lockservice_alloc_lock γ (srv:loc) ln E :
  ↑lockserviceN ⊆ E →
  is_lockserver γ srv -∗
  Ps ln ={E}=∗
  lockservice_is_lock γ ln.
Proof.
  iIntros (?) "Hserver HP". iNamed "Hserver".
  iInv "Hinv" as "Hlockinv".
  (* FIXME: looks like iNamed does not handle the ▷ here *)
  iDestruct "Hlockinv" as (locksAlloc locksMapDom) "(>Hdom & >Hlocks & >HlocksEx & HlocksNew)".
  destruct (locksAlloc !! ln) eqn:Hln.
  - destruct u.
    iDestruct (big_sepM_lookup_acc with "HlocksNew") as "[[#>His_lock Hln] HlocksNew]"; first done.
    iSpecialize ("HlocksNew" with "[$Hln $His_lock]").
    iModIntro. iSplitL; last done. iNext.
    iExists _, locksMapDom. iFrame; iFrame "#".
  - iMod (map_alloc_ro ln () with "Hlocks") as "[Hlocks #Hptsto]"; first eauto.
    iDestruct (big_sepM_later with "HlocksNew") as "HlocksNew".
    iDestruct (big_sepM_insert _ locksAlloc ln () with "[HP $HlocksNew]") as "HlocksNew"; first done.
    { iFrame "#". by iRight. }
    iDestruct (big_sepM_later with "HlocksNew") as "HlocksNew".
    iModIntro. iSplitL; last done. iNext.
    iExists _, locksMapDom. iFrame; iFrame "#".
    iDestruct "HlocksEx" as %HlocksEx. iPureIntro. set_solver.
Qed.

Lemma tryLock_core_spec γ (srv:loc) args :
inv lockserviceInvN (Lockserver_inv γ) -∗
{{{ 
     LockServer_own_core γ srv ∗ TryLock_Pre γ args
}}}
  LockServer__tryLock_core #srv (into_val.to_val args)
{{{
   b, RET #b; LockServer_own_core γ srv
      ∗ TryLock_Post args b
}}}.
Proof.
  iIntros "#Hinv" (Φ) "!# [Hlsown #Hpre] Hpost".
  wp_lam.
  wp_pures.
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
    by iLeft.
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
      set (ln := args.1) in *.
      replace (dom (gset u64) (<[ln:=true]> locksM)) with (dom (gset u64) locksM); first done.
      rewrite dom_insert_L.
      assert (args.1 ∈ dom (gset u64) locksM).
      { apply elem_of_dom. eauto. }
      set_solver.
    + (* The lock did not exist yet, we have to "physically allocate" it. *)
      apply map_get_false in H as [H _].
      iApply fupd_wp.
      iInv "Hinv" as (locksAlloc locksDom) "(>Hdom & >Hlocks & >HlocksEx &  HlocksNew)".
      iDestruct (ghost_var_agree with "HmapDom Hdom") as %<-.
      set (ln := args.1) in *.
      iMod (ghost_var_update_halves ({[ ln ]} ∪ dom (gset _) locksM) with "HmapDom Hdom") as "[HmapDom Hdom]".
      iDestruct (map_valid with "Hlocks Hpre") as %Halloc.
      iDestruct (big_sepM_delete with "HlocksNew") as "[HP HlocksNew]"; first exact Halloc.
      iDestruct "HP" as "[#His_lock [>HP|HP]]".
      { iDestruct "HP" as %HP%elem_of_dom. exfalso.
        destruct HP as [? HP]. rewrite HP in H. done. }
      iModIntro. iSplitL "HlocksNew HlocksEx Hlocks Hdom".
      { iNext. iExists _, _. iFrame "Hdom Hlocks".
        iSplit.
        - iDestruct "HlocksEx" as %HlocksEx. iPureIntro.
          assert (ln ∈ dom (gset _) locksAlloc). { apply elem_of_dom. eauto. }
          set_solver.
        - iFrame "#". iApply (big_sepM_delete _ _ ln); first done. iSplitR.
          { iFrame "#". iLeft. iPureIntro. set_solver. }
          iApply (big_sepM_mono with "HlocksNew").
          intros ln' ? _. simpl. iIntros "[Hptsto [Hln'|Hln']]"; last by eauto.
          iFrame "Hptsto". iLeft. iDestruct "Hln'" as %Hln'.
          iPureIntro. set_solver. }
      iModIntro. wp_pures. iApply "Hpost".

      rewrite /TryLock_Post.
      iSplitR "HP"; last by eauto with iFrame.
      iExists _, _. iFrame.
      rewrite /typed_map.map_insert dom_insert_L. iFrame "HmapDom".
      iApply big_sepM_insert; first done. iFrame "Hlockeds". eauto.
Qed.

Lemma unlock_core_spec γ (srv:loc) args :
{{{
  LockServer_own_core γ srv ∗ Unlock_Pre γ args
}}}
  LockServer__unlock_core #srv (into_val.to_val args)
{{{
   b, RET #b; LockServer_own_core γ srv
      ∗ Unlock_Post args b
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
    set (ln:=args.1) in *.
    replace (dom (gset u64) (<[ln:=false]> locksM)) with (dom (gset u64) locksM); first done.
    rewrite dom_insert_L.
    assert (ln ∈ dom (gset u64) locksM).
    { apply elem_of_dom. eauto. }
    set_solver.
  - wp_pures. iApply "Hpost". iSplitL; eauto.
    iExists _, _; iFrame.
Qed.

Lemma LockServer__TryLock_spec srv γ :
is_lockserver γ srv -∗
{{{
    True
}}}
    LockServer__TryLock #srv
{{{ (f:goose_lang.val), RET f;
        is_rpcHandler f γ.(ls_rpcGN) (TryLock_Pre γ) TryLock_Post
}}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iApply is_rpcHandler_eta; simpl.
  iIntros "!#" (_ _).
  iNamed "Hls". wp_pures.
  wp_loadField.
  iApply (RPCServer__HandleRequest_spec with "[] His_rpc"); last by eauto.
  clear Φ. iIntros (req) "!#". iIntros (Φ) "Hpre HΦ".
  wp_pures.
  iApply (tryLock_core_spec with "Hinv Hpre"); last by eauto.
Qed.

Lemma Clerk__TryLock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    own_lockclerk γ ck srv ∗
    is_lockserver γ srv 
  }}}
    Clerk__TryLock #ck #ln
  {{{ b, RET #b; own_lockclerk γ ck srv ∗ (⌜b = false⌝ ∨ ⌜b = true⌝ ∗ Ps ln) }}}.
Proof using Type*.
  iIntros (Φ) "(#Htok & Hclerk & #Hserver) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply LockServer__TryLock_spec; first eauto.
  iIntros (f) "#Hfspec".
  wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ cl_ptr (ln, (U64(0), ())) γ.(ls_rpcGN) with "[] [Hcl]"); eauto.
  {
    iNamed "Hserver". iNamed "His_rpc". iFrame "# ∗".
  }
  iIntros (v) "Hretv".

  (* Reason about converting the u64 to bool *)
  wp_binop.
  wp_pures.
  iNamed "Hretv".
  iDestruct "Hretv" as "[Hrpcclient HcorePost]".
  iApply "Hpost".
  iSplitL "Hrpcclient Hcl_ptr Hprimary".
  { iExists _; iFrame. }

  iDestruct "HcorePost" as "[HcorePost|HcorePost]".
  { iDestruct "HcorePost" as %->. by iLeft. }
  { iDestruct "HcorePost" as (->) "HP". iRight. iFrame. done. }
Qed.

Lemma LockServer__Unlock_spec srv γ :
is_lockserver γ srv -∗
{{{
    True
}}}
    LockServer__Unlock #srv
{{{ (f:goose_lang.val), RET f;
        is_rpcHandler f γ.(ls_rpcGN) (Unlock_Pre γ) Unlock_Post
}}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iApply is_rpcHandler_eta; simpl.
  iIntros "!#" (_ _).
  iNamed "Hls". wp_pures.
  wp_loadField.
  iApply (RPCServer__HandleRequest_spec with "[] His_rpc"); last by eauto.
  clear Φ. iIntros (req) "!#". iIntros (Φ) "Hpre HΦ".
  wp_pures.
  iApply (unlock_core_spec with "Hpre"); last by eauto.
Qed.

Lemma Clerk__Unlock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    Ps ln ∗
    own_lockclerk γ ck srv ∗
    is_lockserver γ srv 
  }}}
    Clerk__Unlock #ck #ln
  {{{ (b:bool), RET #b; own_lockclerk γ ck srv ∗ True }}}.
Proof using Type*.
  iIntros (Φ) "(#Htok & HP & Hclerk & #Hserver) Hpost".
  wp_lam.
  wp_pures. 
  iNamed "Hclerk".
  repeat wp_loadField.
  wp_apply LockServer__Unlock_spec; first eauto.
  iIntros (f) "#Hfspec".
  wp_loadField.
  wp_apply (RPCClient__MakeRequest_spec _ cl_ptr (ln, (U64(0), ())) γ.(ls_rpcGN) with "[] [Hcl HP]"); eauto.
  {
    iNamed "Hserver". iNamed "His_rpc". iFrame "# ∗".
  }
  iIntros (v) "Hretv".

  (* Reason about converting the u64 to bool *)
  wp_binop.
  wp_pures.
  iNamed "Hretv".
  iDestruct "Hretv" as "[Hrpcclient HcorePost]".
  iApply "Hpost".
  iSplitL "Hrpcclient Hcl_ptr Hprimary".
  { iExists _; iFrame. }

  done.
Qed.

Lemma Clerk__Lock_spec γ ck (srv:loc) (ln:u64) :
  {{{
    lockservice_is_lock γ ln ∗
    own_lockclerk γ ck srv ∗
    is_lockserver γ srv
  }}}
    Clerk__Lock #ck #ln
  {{{ RET #true; own_lockclerk γ ck srv ∗ Ps ln }}}.
Proof using Type*.
  iIntros (Φ) "[#Htok [Hclerk_own #Hinv]] Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_forBreak
              (fun c =>
                 (own_lockclerk γ ck srv ∗ Ps ln -∗ Φ #true)
                 ∗ own_lockclerk γ ck srv
                 ∗ (⌜c = true⌝ ∨ ⌜c = false⌝∗ Ps ln)
              )%I
           with "[] [$Hclerk_own $Hpost]"); eauto.
  {
    iIntros (Ψ).
    iModIntro. iIntros "[HΦpost [Hclerk_own _]] Hpost".
    wp_apply (Clerk__TryLock_spec with "[$Hclerk_own]"); eauto.
    iIntros (tl_r) "[Hown_clerk TryLockPost]".
    destruct tl_r.
    {
      wp_pures.
      simpl.
      iApply "Hpost".
      iFrame. iRight.
      iDestruct "TryLockPost" as "[% | [_ HP]]"; eauto.
      discriminate.
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

Lemma MakeLockServer_spec :
  {{{ True }}}
    MakeLockServer #()
  {{{ γ srv, RET #srv;
    is_lockserver γ srv ∗ [∗ set] cid ∈ fin_to_set u64, lockserver_cid_token γ cid
  }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  iMod make_rpc_server as (γrpc) "(#is_server & server_own & cli_tokens)"; first done.
  iMod (ghost_var_alloc (∅ : gset u64)) as (γdom) "[Hdom1 Hdom2]".
  iMod (map_init (∅ : gmap u64 unit)) as (γlocks) "Hloglocks".
  set (γ := LockserviceNames γrpc γlocks γdom) in *.
  iApply wp_fupd.

  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl". wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_sv & l_locks & _)".
  wp_apply (wp_NewMap bool (t:=boolT)). iIntros (locks) "Hlocks".
  wp_storeField.
  wp_apply (MakeRPCServer_spec (LockServer_own_core γ l) with "[$server_own $is_server l_locks Hlocks Hdom2]").
  { iExists _, _. iFrame. rewrite dom_empty_L. iFrame.
    iApply big_sepM_empty. done. }
  iIntros (sv) "#Hsv".
  wp_storeField.
  iApply ("HΦ" $! γ).
  iFrame "cli_tokens".
  iMod (inv_alloc with "[Hdom1 Hloglocks]") as "$".
  { iExists _, _. iFrame. iSplit.
    - iPureIntro. done.
    - iApply big_sepM_empty. done. }
  iExists sv. replace (γ.(ls_rpcGN)) with γrpc; last done. 
  iMod (readonly_alloc_1 with "l_sv") as "$".
  iModIntro.
  iFrame "#".
Qed.

Lemma MakeLockClerk_spec γ (srv : loc) (cid : u64) :
  {{{ is_lockserver γ srv ∗ lockserver_cid_token γ cid }}}
    MakeClerk #srv #cid
  {{{ ck, RET #ck; own_lockclerk γ ck srv }}}.
Proof.
  iIntros (Φ) "[#Hserver Hcid] HΦ". wp_lam.
  rewrite /lockserver_cid_token /own_lockclerk.
  iApply wp_fupd.

  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl". wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_primary & l_client & _)".
  wp_storeField.
  wp_apply (MakeRPCClient_spec with "Hcid").
  iIntros (cl) "Hcl".
  wp_storeField.
  iApply "HΦ". iExists _.
  by iFrame.
Qed.

End lockservice_proof.
