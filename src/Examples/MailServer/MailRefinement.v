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

Lemma map_Permutation (A B: Type) (f: A → B) (al: list A) (bl: list B):
  Permutation.Permutation (map f al) bl →
  ∃ al', Permutation.Permutation al al' ∧
         map f al' = bl.
Proof.
  intros Hperm.
  remember (map f al) as bl0 eqn:Heq.
  revert Heq.
  revert al.
  induction Hperm => al Heq.
  - destruct al. exists []. eauto.
    inversion Heq.
  - destruct al as [|a al]; inversion Heq; subst.
    simpl in Heq.
    edestruct (IHHperm) as (al'&?&?); eauto.
    subst. exists (a :: al'). split; eauto.
  - destruct al as [|a [| b al]]; try inversion Heq; subst.
    exists (b :: a :: al); split; eauto.
    econstructor.
  - edestruct (IHHperm1) as (al1&?&?); eauto.
    edestruct (IHHperm2) as (al2&?&?); eauto.
    exists al2; split; eauto.
    etransitivity; try eassumption; eauto.
Qed.

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
    (∃ S1 S2, ghost_mapsto_auth γ (A := discreteC contents) S1
      ∗ ghost_mapsto (A := discreteC contents) γ O S2)%I.

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
    iDestruct "HP2" as (v Heq ?) "HP2".
    rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
    iDestruct "HP1" as "(HP1&HR1)".
    iDestruct "HP2" as "(HP2&HR2)".
    iSplitL "HP1 HP2".
    { iExists lsptr, (S q). iFrame. iExists _. by iFrame. }
    iExists _. iFrame. iExists _. by iFrame.
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
    iIntros "Hlockinv". iDestruct "Hlockinv" as (??) "(H1&H2)".
      by iMod (ghost_var_update (A := discreteC contents) with "H1 H2") as "($&$)".
  Qed.

  Lemma slice_mapsto_len {T} (s: slice.t T) (ls: Datatypes.list T) :
    s ↦ ls -∗ ⌜ s.(slice.length) = length ls ⌝.
  Proof.
    iIntros "Hpts". iDestruct "Hpts" as (??) "Hpts". iPureIntro.
    symmetry. eapply getSliceModel_len_inv; eauto.
  Qed.

  Definition readMessage_handle f :=
  (fileContents <- Data.newPtr (slice.t byte);
  initData <- Data.newSlice byte 0;
  _ <- Loop (fun pf =>
        buf <- FS.readAt f pf.(partialFile.off) 4096;
        newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
        if compare_to (slice.length buf) 4096 Lt
        then
          _ <- Data.writePtr fileContents newData;
          LoopRet tt
        else
          Continue {| partialFile.off := pf.(partialFile.off) + slice.length buf;
                      partialFile.data := newData; |}) {| partialFile.off := 0;
           partialFile.data := initData; |};
  fileData <- Data.readPtr fileContents;
  fileStr <- Data.bytesToString fileData;
  Ret fileStr)%proc.

  Lemma readMessage_unfold_open userDir name:
    readMessage userDir name =
    (let! f <- open userDir name;
     readMessage_handle f)%proc.
  Proof. trivial. Qed.
  Opaque readMessage.

  Lemma take_length_lt {A} (l : Datatypes.list A) (n : nat):
    length (take n l) < n → take n l = l.
  Proof.
    intros Hlen. apply take_ge.
    rewrite take_length in Hlen.
    lia.
  Qed.

  Lemma wp_readMessage_handle f inode ls q1 q2 :
    {{{ f ↦{q1} (inode, Read) ∗ inode ↦{q2} ls }}}
      readMessage_handle f
    {{{ RET (bytes_to_string ls); f ↦{q1} (inode, Read) ∗ inode ↦{q2} ls }}}.
  Proof.
    rewrite /readMessage_handle.
    generalize 4096 => k.
    iIntros (Φ) "(Hf&Hinode) HΦ".
    wp_bind.
    iApply (wp_newAlloc with "[//]").
    iIntros (fileContents) "!> HfC".
    wp_bind.
    iApply (@wp_newSlice with "[//]").
    iIntros (fileSlice) "!> (HfS&_)".
    simpl repeat.
    replace [] with (take 0 ls) by auto.
    generalize 0 => idx.
    wp_bind.
    iLöb as "IH" forall (fileSlice idx).
    wp_loop.
    wp_bind.
    iApply (wp_readAt with "[$]").
    iIntros (s) "!> (Hf&Hinode&Hs)".
    wp_bind.
    iApply (wp_sliceAppendSlice with "[HfS Hs]").
    { iFrame. }
    simpl. clear fileSlice.
    iIntros (fileSlice) "!> (HfS&Hs)".
    iDestruct (slice_mapsto_len with "Hs") as %->.
    iClear "Hs".
    destruct lt_dec as [Hlt|Hnlt].
    - wp_bind.
      iApply (wp_writePtr with "[$]").
      iIntros "!> HfC".
      wp_ret.
      iNext.
      wp_ret.
      wp_bind.
      iApply (wp_readPtr with "[$]").
      iIntros "!> HfC".
      wp_bind.
      iApply (wp_bytesToString with "[$]").
      iIntros "!> _".
      wp_ret.
      apply take_length_lt in Hlt.
      rewrite Hlt. rewrite take_drop.
      iApply "HΦ". iFrame.
    - wp_ret.
      iNext.
      iApply ("IH" with "[$] [$] [$] [$]").
      rewrite take_take_drop.
      assert (length (take k (drop idx ls)) = k) as ->; last by eauto.
      cut (length (take k (drop idx ls)) ≤ k); first by lia.
      eapply firstn_le_length.
  Qed.

  Lemma createMessages_length msgs:
    length (createMessages msgs) = length msgs.
  Proof. by rewrite map_length. Qed.

  Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) msgs E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Pickup_End uid msgs)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MPickingUp, v) ⌝ ∗
        j ⤇ K (Call (Pickup_End uid msgs)) ∗ source_state σ.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - destruct v as ([]&?).
      * iIntros.  iFrame. eauto.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ _
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma nth_error_map {A B: Type} (f:A → B) (n: nat) l (b: B):
    nth_error (map f l) n = Some b → ∃ a, f a = b ∧ nth_error l n = Some a.
  Proof.
    revert l. induction n => l //=.
    * destruct l as [| a l] => //=. intros. exists a; split; congruence.
    * destruct l as [| a l] => //=. intros. eauto.
  Qed.

  Lemma take_snoc_S {A} (ls: List.list A) (i: nat) a :
    nth_error ls i = Some a →
    take (i + 1) ls = take i ls ++ [a].
  Proof.
    intros Hin. revert ls Hin. induction i => ls Hin.
    - rewrite //=. destruct ls; inversion Hin; subst.
      simpl. by rewrite firstn_O.
    - rewrite //=. destruct ls; inversion Hin.
      simpl. f_equal. eauto.
  Qed.

  Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Unlock uid)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MLocked, v) ⌝ ∗
        j ⤇ K (Call (Unlock uid)) ∗ source_state σ.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - destruct v as ([]&?).
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
      * iIntros. iFrame. eauto.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ _
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma unlock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid:
    {{{ j ⤇ K (Call (Unlock uid)) ∗ Registered ∗ ExecInv }}}
      MailServer.Unlock uid
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
    iMod (unlock_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
    { solve_ndisj. }
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk γ) "(%&%&#Hlock&Hinbox)".
    iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
    iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
    { intros. econstructor. eexists; split; last by econstructor.
      econstructor; eauto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq. eauto.
      - simpl. do 2 eexists; split; econstructor.
    }
    { solve_ndisj. }
    iExists _. iFrame.
    iExists _. iFrame.
    iDestruct "Hmbox" as "(Hwlock&Hlockinv&Hunlocked)".
    iSplitL "Hm Hmsgs Hdircontents Hunlocked".
    { iModIntro.  iNext. iApply "Hm". iExists _, _.
      do 2 (iSplitL ""; eauto).
      iFrame. iFrame "Hlock".
    }
    iModIntro.
    wp_bind. iApply (wp_sliceRead with "[$]").
    { eauto. }
    iIntros "!> Hlsptr".
    iApply (wp_lockRelease_writer with "[Hwlock Hlockinv]"); swap 1 2.
    { iFrame "Hlock"; iFrame. }
    { set_solver+. }
    iIntros "!> _". iApply "HΦ". iFrame.
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

    wp_bind. 
    iApply (wp_lockAcquire_writer with "Hlock").
    { set_solver+. }
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
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid (discreteC contents) with "Hauth Hauth'").
    }
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
      iDestruct "Hauth" as (S ?) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid (discreteC contents) with "Hauth Hauth'").
    }
    iDestruct "Hmbox" as "[>Hmbox|Hmbox]"; last first.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S ?) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
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
    iIntros (s lmsg_names) "!> (Hperm&Hslice_list&Hdircontents&Hdirlock)".
    iDestruct "Hperm" as %Hperm.
    (* Simulate the first step of Pickup here, since we've finished readdir *)
    rewrite -map_to_list_dom_perm in Hperm *.
    intros Hperm. symmetry in Hperm.
    edestruct (map_Permutation) as (msgs'&Hperm'&Hmsgs'_map); first by eauto.
    iMod (ghost_step_call _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x)))) msgs'
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
    { intros. econstructor. eexists; split; last by econstructor.
      econstructor; eauto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq. eauto.
      - simpl. do 2 eexists; split; last first.
        * econstructor; eauto. by symmetry.
        * econstructor.
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
    iIntros (messages0) "!> Hmessages0".
    wp_bind.
    iApply (wp_newSlice with "[//]").
    iIntros (messages') "!> (Hmessages&_)".
    wp_bind.
    iApply (wp_writePtr with "[$]").
    iIntros "!> Hmessages0".
    wp_bind.
    (* Begin loop *)
    simpl repeat.

    iDestruct (slice_mapsto_len with "Hslice_list") as %->.

    (* Get induction hypothesis into shape *)
    remember [] as lmsgs_read eqn:Heq_lmsgs_read.
    assert (length lmsg_names = length msgs').
    { by rewrite -Hmsgs'_map map_length. }
    assert (lmsgs_read = createMessages (take O msgs')) as Hread_ind.
    { by eauto. }
    assert (exists k, 0 + k = length lmsg_names) as Hk by (exists (length lmsg_names); lia).
    revert Hk.
    assert (length lmsgs_read = 0) as Hlen by (rewrite Heq_lmsgs_read //=).
    move: Hlen.
    assert (∃ i, i = 0) as (i&Heq_i) by eauto.
    rewrite -{1}Heq_i.
    rewrite -{1}Heq_i.
    rewrite -[a in Loop _ a]Heq_i.
    rewrite -Heq_i in Hread_ind.
    replace (messages'.(slice.length) = 0) with
        (messages'.(slice.length) = i) by congruence.
    clear Heq_i => Hlen.
    clear Heq_lmsgs_read.
    intros (k&Hk).

    iMod (ghost_step_bind_ret with "Hj Hsource") as "Hj".
    { solve_ndisj. }
    iInduction k as [|k] "IH" forall (messages' i lmsgs_read Hread_ind Hlen Hk); last first.
    - wp_loop.
      destruct equal as [Heq_bad|].
      { exfalso. rewrite Heq_bad in Hk. lia. }
      assert (i < length lmsg_names).
      { lia. }
      destruct (nth_error lmsg_names i) as [curr_name|] eqn:Heq_name1; last first.
      { exfalso. eapply nth_error_Some; eauto. }
      wp_bind. iApply (wp_sliceRead with "Hslice_list"); first eauto.
      iIntros "!> Hslice_list".
      wp_bind.
      rewrite readMessage_unfold_open.
      wp_bind.
      clear σ Heq.
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap)".
      iMod (pickup_end_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      iDestruct "Hmsgs" as (ls') "(>Hglobal&Hm)".
      iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
      iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
      iDestruct "Huid" as (??) "(>Heq1&>Heq2&Hinbox)".
      iDestruct "Heq1" as %Heq1'.
      iDestruct "Heq2" as %Heq2'.
      iDestruct "Hinbox" as "(Hlock'&Hmbox&>Hdircontents&>Hmsgs)".
      assert (H7 = lk) by congruence. subst.
      assert (H8 = γ) by congruence. subst.
      iDestruct "Hmbox" as ">(Hwlock&Hlockinv)".
      iDestruct "Hlockinv" as (S) "(Hauth&Hsubset)".
      iDestruct "Hsubset" as %Hsubset.
      iDestruct (ghost_var_agree (A := discreteC contents) with "Hauth Hcontents_frag") as %?.
      subst.
      assert (∃ body, msgs !! curr_name = Some body ∧
             nth_error msgs' i = Some (curr_name, body)) as (body&Hmsgs_curr_name&Hmsgs'_curr_name).
      {
        apply nth_error_map in Heq_name1 as (mbody&Heq_body&Hnth_name1).
        apply nth_error_In in Hnth_name1 as Hin.
        destruct mbody as (?&body). simpl in Heq_body. subst.
        exists body.
        apply elem_of_list_In in Hin. split.
        * rewrite -Hperm' in Hin *. apply elem_of_map_to_list.
        * eauto.
      }
      iDestruct (big_sepM_lookup_acc with "Hmsgs") as "(Hcurr_msg&Hmsgs)"; eauto.
      { eapply lookup_weaken; last eassumption. eauto. }
      iDestruct "Hcurr_msg" as (inode q) "(Hpath&Hinode)".
      iApply (wp_open with "[$]").
      iIntros (fh) "!> (Hpath&Hfh)".
      iPoseProof (@Count_GHeap.read_split_join with "Hinode") as "(Hinode_inv&Hinode)".
      iExists _. iFrame.
      iSplitL "Hm Hinode_inv Hmsgs Hglobal Hauth Hwlock Hdircontents Hpath".
      { iModIntro. iNext. iExists _. iFrame. iApply "Hm".
        iExists _, _. iFrame.
        iSplitL ""; first by eauto.
        iSplitL ""; first by eauto.
        iFrame "Hlock". iExists _. iFrame.
        iSplitL ""; first by eauto.
        iApply "Hmsgs". iExists _, (S q). iFrame.
      }
      iModIntro.
      iApply (wp_readMessage_handle with "[$]").
      iIntros "!> (Hfh&Hinode)".
      wp_bind.
      iApply (wp_readPtr with "[$]").
      iIntros "!> Hmessages0".
      wp_bind.
      iApply (wp_sliceAppend with "Hmessages").
      rename messages' into messages_old.
      iIntros (messages') "!> Hmessages".
      wp_bind.
      iApply (wp_writePtr with "Hmessages0").
      iIntros "!> Hmessages0".
      wp_ret.
      iNext. iApply ("IH" with "[] [] [] [$] HΦ [$] [$] [$] [$] [$] [$] [$] [$]").
      * iPureIntro.
        rewrite -(map_app _ _ ([ (curr_name, body)])).
        f_equal.
        erewrite take_snoc_S; eauto.
      * iPureIntro. rewrite app_length Hlen //=.
      * iPureIntro. lia.
    - wp_loop.
      rewrite right_id in Hk * => Hlen_names.
      rewrite Hlen_names.
      destruct equal as [_|]; last by congruence.
      assert (i = length msgs').
      { congruence. }
      assert (lmsgs_read = createMessages msgs').
      {
        subst. rewrite map_length. by rewrite firstn_all.
      }
      subst. rewrite map_length. rewrite firstn_all.
      wp_ret.
      iNext.
      iInv "Hinv" as "H".
      clear σ Heq.
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap)".
      (* Show messages' ptr can't be in σ, else we'd have a redundant pts to *)
      iDestruct (slice_mapsto_non_null with "Hmessages") as %?.
      iAssert (⌜ Data.getAlloc messages'.(slice.ptr) σ.(heap) = None /\
               messages'.(slice.ptr) <> nullptr _ ⌝)%I with "[-]" as %?.
      { iSplit; last auto.
        destruct (Data.getAlloc messages'.(slice.ptr) σ.(heap)) as [v|] eqn:Heq_get; last by done.
        iExFalso.
        rewrite /HeapInv.
        rewrite /Data.getAlloc in Heq_get.
        iPoseProof (big_sepDM_lookup (T:=(Ptr.Heap Message.t))
                      (dec := sigPtr_eq_dec) with "Hheap") as "Hheap"; eauto.
        iDestruct "Hmessages" as (???) "Hmessages".
        iApply (Count_Typed_Heap.mapsto_valid_generic with "[Hmessages] Hheap"); try iFrame.
        { lia. }
        { eauto. lia. }
      }
      iMod (pickup_end_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      iDestruct "Hmessages" as (malloc Hmalloc) "Hmessages".
      iMod (ghost_step_call _ _ _ messages'
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; last eauto.
        do 2 eexists.
        split.
        { rewrite /lookup/readSome. rewrite Heq. eauto. }
        reduce.
        do 2 eexists. split.
        { simpl. econstructor.  }
        do 2 eexists. split.
        { simpl. econstructor. }
        do 2 eexists. split.
        { econstructor. eauto. }
        eexists (_, _), _. split.
        { econstructor. split; eauto. }
        do 2 eexists. split.
        { econstructor. }
        econstructor.
      }
      { solve_ndisj. }
      wp_ret.
      iExists _. iFrame.
      iSplitR "Hj Hmessages0 HΦ Hreg".
      { iModIntro. iNext.
        iSplitL "Hmsgs Hcontents_frag Hdirlock".
        { simpl. rewrite /MsgsInv. iDestruct "Hmsgs" as (l0) "(?&Hmap)".
          iExists _. iFrame.
          simpl.
          iApply (big_sepM_insert_override_2 with "Hmap"); eauto.
          rewrite /MsgInv. simpl.
          iIntros "H". iDestruct "H" as (lk' γ') "(%&%&(?&Hinterp&?&?))".
          iExists _, _. iFrame.
          iDestruct "Hinterp" as "(?&Hinterp)". iFrame.
          iDestruct "Hinterp" as (S) "(Hauth&_)".
          iFrame "%".
          iExists _, _.  iFrame.
          assert (γ' = γ) as -> by congruence.
          iFrame.
        }
        unfold HeapInv.
        simpl.
        rewrite big_sepDM_updDyn; last first.
        { intuition. }
        iFrame.
        iDestruct "Hmessages" as (?) "Hm". eauto.
      }
      iModIntro. wp_bind.
      iApply (wp_readPtr with "[$]").
      iIntros "!> Hptr". wp_ret. iApply "HΦ". iFrame.
  Time Qed.


End refinement_triples.