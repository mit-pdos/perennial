From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Unset Implicit Arguments.

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Set Default Goal Selector "!".

Notation contents := (gmap string (Datatypes.list byte)).
Canonical Structure contentsC {m: GoModel} {wf: GoModelWf m} :=
  leibnizC contents.

Definition UserDir {model: GoModel} (user:uint64) :=
  ("user" ++ uint64_to_string user)%string.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ,
            ghost_mapG (discreteC contents) Σ}.
  (*
  Context `{Hghost_path: gen_dirPreG string string (Inode) Σ}.
  Context `{Hghost_dirset: gen_heapPreG string (gset string) Σ}.
   *)

  Import Filesys.FS.
  Import GoLayer.Go.
  Import Mail.


  (* Every pointer in the abstract state should have a matching
     pointer with the same value in the concrete state. *)
  Definition HeapInv (σ : Mail.State) : iProp Σ :=
    ([∗ dmap] p↦v ∈ (Data.allocs σ.(heap)),
       Count_Typed_Heap.mapsto (hG := go_heap_inG) p O (fst v) (snd v))%I.

  Definition InboxLockInv (γ: gname) (n: nat) :=
    (∃ S, ghost_mapsto_auth γ (A := discreteC contents) S
      ∗ ghost_mapsto (A := discreteC contents) γ O S)%I.

  Definition MailboxStatusInterp (uid: uint64) (lk: LockRef) (γ: gname)
             (ls: MailboxStatus) (msgs: contents) :=
    (match ls with
     | MUnlocked => UserDir uid ↦ Unlocked
        ∨ (UserDir uid ↦{-1} ReadLocked 0 ∗ InboxLockInv γ O)
     | MPickingUp => wlocked lk
        ∗ ∃ (S: contents), ghost_mapsto_auth γ (A := discreteC contents) S ∗ ⌜ S ⊆ msgs ⌝
     | MLocked => wlocked lk ∗ InboxLockInv γ O ∗ UserDir uid ↦ Unlocked
     end)%I.

  Definition boxN : namespace := (nroot.@"inbox_lock").

  Definition InboxInv (uid: uint64) (lk: LockRef) (γ: gname) (ls: MailboxStatus)
             (msgs: gmap.gmap string (Datatypes.list byte)) :=
    (is_lock boxN lk (InboxLockInv γ) True
     ∗ MailboxStatusInterp uid lk γ ls msgs
     ∗ UserDir uid ↦ dom (gset string) msgs
     ∗ ([∗ map] mid ↦ msgData ∈ msgs,
        ∃ inode (n: nat), path.mk (UserDir uid) mid ↦ inode
                ∗ inode ↦{n} msgData))%I.

  Definition GlobalInv ls : iProp Σ :=
    (∃ (lsptr: slice.t LockRef) (q: nat), global ↦{q} Some lsptr ∗ lsptr ↦{q} ls)%I.


  Lemma GlobalInv_split ls :
    GlobalInv ls ⊢ GlobalInv ls ∗ ∃ lsptr, global ↦{-1} Some lsptr ∗ lsptr ↦{-1} ls.
  Proof.
    iIntros "HG".
    iDestruct "HG" as (lsptr q) "(HP1&HP2)".
    iDestruct "HP2" as (v Heq) "HP2".
    rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
    iDestruct "HP1" as "(HP1&HR1)".
    iDestruct "HP2" as "(HP2&HR2)".
    iSplitL "HP1 HP2".
    { iExists lsptr, (S q). iFrame. iExists _. eauto. }
    iExists _. iFrame. iExists _. eauto.
  Qed.

  Definition MsgInv (Γ: gmap uint64 gname) ls uid lm : iProp Σ :=
      (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
      ∗ ⌜ List.nth_error ls uid = Some lk ⌝
      ∗ InboxInv uid lk γ (fst lm) (snd lm))%I.

  Definition MsgsInv (Γ : gmap uint64 gname) (σ: Mail.State) : iProp Σ :=
    (∃ ls, GlobalInv ls ∗ ([∗ map] uid↦lm ∈ σ.(messages), MsgInv Γ ls uid lm))%I.

  Lemma MsgInv_pers_split Γ ls uid lm :
    MsgInv Γ ls uid lm -∗
           (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
                  ∗ ⌜ List.nth_error ls uid = Some lk ⌝
                  ∗ (is_lock boxN lk (InboxLockInv γ) True)).
  Proof.
    iIntros "HG".
    iDestruct "HG" as (lk γ Hlookup1 Hlookup2) "(#Hlock&HI)".
    iExists _, _. iFrame "%". iFrame "Hlock".
  Qed.

  Lemma MsgsInv_pers_split Γ σ ls uid v:
    σ.(messages) !! uid = Some v →
    ([∗ map] uid↦lm ∈ σ.(messages), MsgInv Γ ls uid lm)
    -∗ (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
                ∗ ⌜ List.nth_error ls uid = Some lk ⌝
                ∗ (is_lock boxN lk (InboxLockInv γ) True)).
  Proof.
    iIntros (?) "Hm".
    iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct (MsgInv_pers_split with "Huid") as "$".
  Qed.

  (* TODO: need to link spool paths to inodes so we can unlink during recovery *)
  Definition TmpInv : iProp Σ :=
    (∃ tmps, SpoolDir ↦ tmps)%I.

  Definition execN : namespace := (nroot.@"msgs_inv").

  (*
  Definition msgsN : namespace := (nroot.@"msgs_inv").
  Definition heapN : namespace := (nroot.@"heap_inv").
   *)
  Instance InboxLockInv_Timeless γ n:
    Timeless (InboxLockInv γ n).
  Proof. apply _. Qed.

  Instance HeapInv_Timeless σ:
    Timeless (HeapInv σ).
  Proof. apply _. Qed.

  Definition ExecInv :=
    (∃ Γ, source_ctx ∗ inv execN (∃ σ, source_state σ ∗ MsgsInv Γ σ ∗ HeapInv σ))%I.

  Global Instance source_state_inhab:
    Inhabited State.
  Proof. eexists. exact {| heap := ∅; messages := ∅ |}. Qed.

  Global Instance LockRef_inhab:
    Inhabited LockRef.
  Proof. eexists. apply nullptr. Qed.

  Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (pickup uid) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ ∃ v, σ.(messages) !! uid = Some v ⌝.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - iIntros; iPureIntro; eauto.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x))))
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma pickup_step_inv' {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    σ.(messages) !! uid = None →
    j ⤇ K (pickup uid) -∗ source_ctx -∗ source_state σ
    ={E}=∗ False.
  Proof.
    - iIntros (? Hnone) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x))))
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Hnone //.
  Qed.

  Lemma GlobalInv_unify lsptr ls ls':
    global ↦{-1} Some lsptr -∗ lsptr ↦{-1} ls -∗ GlobalInv ls' -∗ ⌜ ls = ls' ⌝.
  Proof.
    iIntros "Hgptr Hlsptr HG".
    iDestruct "HG" as (lsptr' ?) "(Hgptr'&Hlsptr')".
    rewrite //=.
    iDestruct (ghost_var_agree2 (A := discreteC sliceLockC) with "Hgptr Hgptr'") as %Heq.
    inversion Heq; subst.
    iApply (slice_agree with "Hlsptr Hlsptr'").
  Qed.

  Set Nested Proofs Allowed.
  Lemma InboxLockInv_set_msgs γ n S :
    InboxLockInv γ n ==∗ ghost_mapsto_auth γ (A := discreteC contents) S
                 ∗ ghost_mapsto (A := discreteC contents) γ O S.
  Proof.
    iIntros "Hlockinv". iDestruct "Hlockinv" as (?) "(H1&H2)".
      by iMod (ghost_var_update (A := discreteC contents) with "H1 H2") as "($&$)".
  Qed.

  Lemma pickup_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid:
    {{{ j ⤇ K (pickup uid) ∗ Registered ∗ ExecInv }}}
      Pickup uid
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ) "(#Hsource&#Hinv)".
    wp_bind.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap)".
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hm)".
    iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
    iDestruct "Hread" as (lsptr) "(Hglobal_read&Hlsptr)".
    iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read".

    destruct (σ.(messages) !! uid) as [v|] eqn:Heq; last first.
    {
      iMod (pickup_step_inv' with "[$] [$] [$]") as %[]; eauto.
      { solve_ndisj. }
    }
    iDestruct (MsgsInv_pers_split with "Hm") as "#Huid"; first eauto.
    iDestruct "Huid" as (lk γ HΓlookup Hnth) "#Hlock".

    (* re-do invariant *)
    iExists _. iFrame. iExists _. iFrame.

    iModIntro.
    wp_bind. iApply (wp_sliceRead with "[$]").
    { eauto. }
    iIntros "!> Hlsptr".

    wp_bind. iApply (wp_lockAcquire_writer with "[$]").
    iIntros "!> (Hlockinv&Hlocked)".
    wp_bind. wp_ret.
    wp_bind.


    wp_bind.
    iInv "Hinv" as "H".
    clear σ Heq v.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap)".
    iDestruct "Hmsgs" as (ls') "(>Hglobal&Hm)".
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq; last first.
    {
      iMod (pickup_step_inv' with "[$] [$] [$]") as %[]; eauto.
      { solve_ndisj. }
    }

    iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
    iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (??) "(>Heq1&>Heq2&Hinbox)".
    iDestruct "Heq1" as %Heq1.
    iDestruct "Heq2" as %Heq2.
    iDestruct "Hinbox" as "(_&Hmbox&Hdircontents&Hmsgs)".
    assert (H5 = lk) by congruence. subst.
    assert (H6 = γ) by congruence. subst.
    destruct v as (status&msgs).
    destruct status.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S) "(Hauth&%)".
      iExFalso.
      iDestruct "Hlockinv" as (S') "(Hauth'&?)".
      iApply (@ghost_var_auth_valid (discreteC contents) with "Hauth Hauth'").
    }
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
      iDestruct "Hauth" as (S) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S') "(Hauth'&?)".
      iApply (@ghost_var_auth_valid (discreteC contents) with "Hauth Hauth'").
    }
    iDestruct "Hmbox" as "[>Hmbox|Hmbox]"; last first.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S') "(Hauth'&?)".
      iApply (@ghost_var_auth_valid (discreteC contents) with "Hauth Hauth'").
    }

    iApply (wp_list_start with "Hmbox").
    iIntros "!> Hmbox".
    iModIntro.
    iExists _. iFrame.
    iExists _. iFrame.
    replace 0%Z with (O: Z) by auto.
    iPoseProof (@Count_Heap.read_split_join1 with "Hmbox") as "(Hrl&Hmbox)".
    iSplitL "Hm Hmbox Hdircontents Hmsgs Hlockinv".
    { iNext.
      iApply "Hm". iExists _, _. iFrame "%".
      iFrame "Hlock". iFrame.
      iRight. iFrame.
    }


    iInv "Hinv" as "H".
    clear σ Heq Heq1 Heq2 msgs.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap)".
    iDestruct "Hmsgs" as (ls') "(>Hglobal&Hm)".
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq; last first.
    {
      iMod (pickup_step_inv' with "[$] [$] [$]") as %[]; eauto.
      { solve_ndisj. }
    }

    iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (??) "(>Heq1&>Heq2&Hinbox)".
    iDestruct "Heq1" as %Heq1.
    iDestruct "Heq2" as %Heq2.
    iDestruct "Hinbox" as "(_&Hmbox&>Hdircontents&Hmsgs)".
    assert (H5 = lk) by congruence. subst.
    assert (H6 = γ) by congruence. subst.
    destruct v as (status&msgs).
    destruct status.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iExFalso.
      iApply (wlocked_wlocked with "Hlocked Hlocked'").
    }
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
      iExFalso.
      iApply (wlocked_wlocked with "Hlocked Hlocked'").
    }
    iDestruct "Hmbox" as "[>Hmbox|>Hmbox]".
    { iExFalso. iApply (@Count_Heap.mapsto_valid_generic with "Hrl Hmbox"); lia. }
    iDestruct "Hmbox" as "(Hrl'&Hlockinv)".
    iPoseProof (@Count_Heap.read_split_join1 with "[Hrl Hrl']") as "Hrl".
    { iFrame.  }
    iApply (wp_list_finish with "[$]").
    iIntros (s lmsgs) "!> (Hperm&Hslice_list&Hdircontents&Hdirlock)".
    iDestruct "Hperm" as %Hperm.
    (* Simulate the first step of Pickup here, since we've finished readdir *)
    iMod (ghost_step_call _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x))))
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
    { intros. econstructor. eexists; split; last by econstructor.
      econstructor; eauto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq. eauto.
      - simpl. do 2 eexists; split; last by eauto.
        econstructor.
    }
    { solve_ndisj. }


    iMod (InboxLockInv_set_msgs _ _ msgs with "[$]") as "(Hcontents_auth&Hcontents_frag)".
    iModIntro.
    iExists _. iFrame.
    iExists _. iFrame.
    replace 0%Z with (O: Z) by auto.

    iSplitL "Hm Hlocked Hcontents_auth Hdircontents Hmsgs".
    { iNext.
      iApply "Hm". iExists _, _.
      iSplitL ""; first by eauto.
      iSplitL ""; first by eauto.
      iFrame "Hlock". iFrame.
      iExists _; iFrame. eauto.
    }

    (* Begin creating message slices *)
    wp_bind.
    iApply (wp_newAlloc with "[//]").
    iIntros (messages) "!> Hmessages".
    wp_bind. wp_bind.
    iApply (wp_newAlloc with "[//]").
    iIntros (initMessages0) "!> Hinit".
    wp_ret.
    wp_bind.
    iApply (wp_writePtr with "[$]").
    iIntros "!> Hmessages".
    wp_bind.
    (* Begin loop *)
  Abort.



End refinement_triples.