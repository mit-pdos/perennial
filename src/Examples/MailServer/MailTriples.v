From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Perennial.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap.
From Perennial.Goose.Examples Require Import MailServer.
From Perennial.Goose.Proof Require Import Interp.
Require Import Goose.Proof.Interp.
From Perennial Require AtomicPair.Helpers.
From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Perennial.Goose Require Import Machine.
From Perennial.Goose Require Import GoZeroValues.

Import Transitions.Relations Coq.Lists.List.

Unset Implicit Arguments.

Inductive ghost_init_status {gm: GoModel} {gmwf: GoModelWf gm} :=
| Uninit
| Started_Init (j: nat) {T2} K `{LanguageCtx _ unit T2 Mail.l K}
| Finished_Init.

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
  leibnizO contents.
Canonical Structure contentsF {m: GoModel} {wf: GoModelWf m} :=
  discreteO contents.

Canonical Structure ghost_init_statusC {m: GoModel} {wf: GoModelWf m} :=
  leibnizO ghost_init_status.
Canonical Structure ghost_init_statusF {m: GoModel} {wf: GoModelWf m} :=
  discreteO ghost_init_status.

Definition UserDir {model: GoModel} (user:uint64) :=
  ("user" ++ uint64_to_string user)%string.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ}.
  Context {hGcontents: ghost_mapG contentsC Σ}.
  Context {hGinit: ghost_mapG ghost_init_statusC Σ}.
  Context {hGTmp: gen_heapG string Filesys.FS.Inode Σ}.
Import Filesys.FS.
Import GoLayer.Go.
Import Mail.


  Definition InboxLockInv (γ: gname) (n: nat) :=
    (∃ S1 S2, ghost_mapsto_auth γ (A := discreteO contents) S1
      ∗ ghost_mapsto (A := discreteO contents) γ O S2)%I.


  Definition MailboxStatusInterp (uid: uint64) (lk: LockRef) (γ: gname)
             (ls: MailboxStatus) (msgs: contents) (open: bool) :=
    (if open then
       match ls with
       | MUnlocked => UserDir uid ↦ Unlocked
          ∨ (UserDir uid ↦{-1} ReadLocked 0 ∗ InboxLockInv γ O)
       | MPickingUp => wlocked lk
          ∗ ∃ (S: contents), ghost_mapsto_auth γ (A := contentsC) S ∗ ⌜ S ⊆ msgs ⌝
       | MLocked => wlocked lk ∗ InboxLockInv γ O ∗ UserDir uid ↦ Unlocked
       end
     else
       ⌜ ls = ls ⌝ ∗ UserDir uid ↦ Unlocked)%I.

  Definition boxN : namespace := (nroot.@"inbox_lock").

  Definition InboxInv (uid: uint64) (lk: LockRef) (γ: gname) (ls: MailboxStatus)
             (msgs: gmap.gmap string (Datatypes.list byte)) (open: bool) :=
    ((if open then is_lock boxN lk (InboxLockInv γ) True else True)
     ∗ MailboxStatusInterp uid lk γ ls msgs open
     ∗ UserDir uid ↦ dom (gset string) msgs
     ∗ ([∗ map] mid ↦ msgData ∈ msgs,
        ∃ inode (n: nat), path.mk (UserDir uid) mid ↦ inode
                ∗ inode ↦{n} msgData))%I.

  Definition InboxInv_weak (uid: uint64) (lk: LockRef) (γ: gname) (ls: MailboxStatus)
             (msgs: gmap.gmap string (Datatypes.list byte)) (open: bool) :=
     (MailboxStatusInterp uid lk γ ls msgs open
     ∗ UserDir uid ↦ dom (gset string) msgs
     ∗ ([∗ map] mid ↦ msgData ∈ msgs,
        ∃ inode (n: nat), path.mk (UserDir uid) mid ↦ inode
                ∗ inode ↦{n} msgData))%I.

  Global Instance InboxInv_timeless uid lk γ ls msgs open':
    Timeless (InboxInv_weak uid lk γ ls msgs open').
  Proof. rewrite /InboxInv_weak. destruct ls, open'; apply _. Qed.

  Definition GlobalInv ls (open: bool): iProp Σ :=
    (if open then
       ∃ (lsptr: slice.t LockRef) (q: nat), global ↦{q} Some lsptr ∗ lsptr ↦{q} (ls, ls)
     else
       global ↦ None)%I.

  Lemma GlobalInv_split ls :
    GlobalInv ls true ⊢ GlobalInv ls true ∗ ∃ lsptr, global ↦{-1} Some lsptr ∗ lsptr ↦{-1} (ls, ls).
  Proof.
    iIntros "HG".
    iDestruct "HG" as (lsptr q) "(HP1&HP2)".
    iDestruct "HP2" as (Heq ?) "HP2".
    rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
    iDestruct "HP1" as "(HP1&HR1)".
    iDestruct "HP2" as "(HP2&HR2)".
    iSplitL "HP1 HP2".
    { iExists lsptr, (S q). iFrame.  by iFrame. }
    iExists _. iFrame. by iFrame.
  Qed.

  Definition MsgInv (Γ: gmap uint64 gname) ls uid lm (open: bool) : iProp Σ :=
      (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
      ∗ ⌜ if open then List.nth_error ls uid = Some lk else True ⌝
      ∗ InboxInv uid lk γ (fst lm) (snd lm) open)%I.

  Definition MsgInv_weak (Γ: gmap uint64 gname) uid lm (open: bool) : iProp Σ :=
      (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝ ∗ InboxInv_weak uid lk γ (fst lm) (snd lm) open)%I.

  Global Instance MsgInv_weak_timeless Γ uid x open:
    Timeless (MsgInv_weak Γ uid x open).
  Proof. rewrite /MsgInv_weak. apply _. Qed.

  Definition userRange_ok (s: gset uint64) :=
    (forall (uid: uint64),
        (uid < 100 -> uid ∈ s) /\
        (uid >= 100 -> ¬ uid ∈ s)).

  Definition RootDirInv (σ: Mail.State) : iProp Σ :=
    (rootdir ↦{-1} ((set_map UserDir (dom (gset uint64) σ.(messages))) ∪ {[ SpoolDir ]})
      ∗ ⌜ userRange_ok (dom (gset uint64) (σ.(messages))) ⌝)%I.

  Lemma RootDirInv_range_ok σ :
    RootDirInv σ -∗ ⌜ userRange_ok (dom (gset _) (σ.(messages))) ⌝.
  Proof. by iIntros "(?&$)". Qed.

  Lemma userRange_ok_eq s s':
    userRange_ok s →
    userRange_ok s' →
    s = s'.
  Proof.
    rewrite /userRange_ok => Hok1 Hok2.
    rewrite -leibniz_equiv_iff => i.
    clear -Hok1 Hok2.
    destruct (Hok1 i) as (Hlt1&Hge1).
    destruct (Hok2 i) as (Hlt2&Hge2).
    destruct (lt_dec i 100) as [Hlt|Hnlt].
    - intuition.
    - assert (i >= 100) by lia. intuition.
  Qed.

  Definition InitInv (Γ: gmap uint64 gname) γ σ :=
    (∃ v : ghost_init_status, ghost_mapsto_auth γ v ∗
    match v with
      | Uninit =>
        ghost_mapsto γ O v ∗ ⌜ σ.(open) = false ⌝
        ∗ ([∗ map] uid↦lm ∈ σ.(messages), ∃ γuid, ⌜ Γ !! uid = Some γuid ⌝ ∗ InboxLockInv γuid O)
      | Started_Init j K =>
        j ⤇ K (Call Open) ∗ ⌜ σ.(open) = false ⌝
      | Finished_Init =>
        ⌜ σ.(open) = true ⌝
      end)%I.

  Definition MsgsInv (Γ : gmap uint64 gname) (γ: gname) (σ: Mail.State) : iProp Σ :=
    (∃ ls, GlobalInv ls σ.(open) ∗ RootDirInv σ ∗ InitInv Γ γ σ
                     ∗ ([∗ map] uid↦lm ∈ σ.(messages), MsgInv Γ ls uid lm σ.(open)))%I.

  Lemma MsgInv_pers_split Γ ls uid lm :
    MsgInv Γ ls uid lm true -∗
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
    ([∗ map] uid↦lm ∈ σ.(messages), MsgInv Γ ls uid lm true)
    -∗ (∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
                ∗ ⌜ List.nth_error ls uid = Some lk ⌝
                ∗ (is_lock boxN lk (InboxLockInv γ) True)).
  Proof.
    iIntros (?) "Hm".
    iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct (MsgInv_pers_split with "Huid") as "$".
  Qed.

  Lemma MsgInv_weaken Γ lks uid lm open:
    MsgInv Γ lks uid lm open -∗ MsgInv_weak Γ uid lm open.
  Proof.
    iIntros "H". iDestruct "H" as (lk γ Hlookup) "(_&Hinbox)".
    iExists _, _. iSplitL ""; auto.
    iDestruct "Hinbox" as "(?&Hmb&?&?)".
    iFrame.
  Qed.

  Global Instance tmp_gen_mapsto `{gooseG Σ} : GenericMapsTo _ _
    := {| generic_mapsto := λ l q v, Count_GHeap.mapsto (hG := hGTmp) l q v|}%I.

  Definition TmpInv : iProp Σ :=
    (∃ tmps_map, SpoolDir ↦ dom (gset string) tmps_map
                          ∗ SpoolDir ↦ Unlocked
                          ∗ gen_heap_ctx tmps_map
                          ∗ [∗ map] name↦inode ∈ tmps_map,
                                      path.mk SpoolDir name ↦ inode
                                      (* ∗ name ↦{1} inode *) )%I.

  Definition execN : namespace := (nroot.@"msgs_inv").

  Global Instance InboxLockInv_Timeless γ n:
    Timeless (InboxLockInv γ n).
  Proof. apply _. Qed.

  Definition ExecInv :=
    (∃ Γ γ, source_ctx ∗ inv execN (∃ σ, source_state σ ∗ MsgsInv Γ γ σ ∗ HeapInv σ ∗ TmpInv))%I.

  Definition ExecInner :=
    (∃ Γ γ σ, ⌜ σ.(open) = false ⌝ ∗ source_state σ ∗ MsgsInv Γ γ σ ∗ HeapInv σ ∗ TmpInv)%I.

  Lemma GlobalInv_unify lsptr ls ls':
    global ↦{-1} Some lsptr -∗ lsptr ↦{-1} (ls, ls) -∗ GlobalInv ls' true -∗ ⌜ ls = ls' ⌝.
  Proof.
    iIntros "Hgptr Hlsptr HG".
    iDestruct "HG" as (lsptr' ?) "(Hgptr'&Hlsptr')".
    rewrite //=.
    iDestruct (ghost_var_agree2 (A := discreteO sliceLockC) with "Hgptr Hgptr'") as %Heq.
    inversion Heq; subst.
    iDestruct (slice_agree with "Hlsptr Hlsptr'") as "(?&?)"; eauto.
  Qed.

  Lemma InboxLockInv_set_msgs γ n S :
    InboxLockInv γ n ==∗ ghost_mapsto_auth γ (A := discreteO contents) S
                 ∗ ghost_mapsto (A := discreteO contents) γ O S.
  Proof.
    iIntros "Hlockinv". iDestruct "Hlockinv" as (??) "(H1&H2)".
      by iMod (ghost_var_update (A := discreteO contents) with "H1 H2") as "($&$)".
  Qed.

  Lemma slice_mapsto_len {T} (s: slice.t T) (ls0 ls: Datatypes.list T) :
    s ↦ (ls0, ls) -∗ ⌜ s.(slice.length) = length ls ⌝.
  Proof.
    iIntros "Hpts". iDestruct "Hpts" as (??) "Hpts". iPureIntro.
    symmetry. eapply getSliceModel_len_inv; eauto.
  Qed.

  Lemma slice_mapsto_len' {T} (s: slice.t T) (ls: Datatypes.list T) :
    s ↦ ls -∗ ⌜ s.(slice.length) = length ls ⌝.
  Proof.
    iIntros "Hpts". iDestruct "Hpts" as (??) "Hpts". iPureIntro.
    symmetry. eapply getSliceModel_len_inv; eauto.
  Qed.

  Definition writeBuf {model:GoModel} f (data:slice.t byte) :=
    (Loop (fun buf =>
            if compare_to Lt (slice.length buf) 4096
            then
              _ <- FS.append f buf;
                LoopRet tt
            else
              _ <- FS.append f (slice.take 4096 buf);
              Continue (slice.skip 4096 buf)) data)%proc.

  Lemma slice_take_split {A} k data (bs0 bs: List.list A) q:
    k ≤ data.(slice.length) →
    data ↦{q} (bs0, bs)
         -∗ (slice.take k data) ↦{q} (bs0, take k bs)
         ∗ ((slice.take k data) ↦{q} (bs0, take k bs) -∗ data ↦{q} (bs0, bs)).
  Proof.
    iIntros (Hlen) "H". iDestruct "H" as (HgetSlice) "H".
    iSplitL "H".
    * iFrame.
      iPureIntro. move: HgetSlice. rewrite /Data.getSliceModel//=.
      rewrite /sublist_lookup/mguard/option_guard.
      destruct decide_rel; last by inversion 1.
      destruct decide_rel; last by lia.
      inversion 1. subst. f_equal.
      rewrite take_take.
      f_equal. lia.
    * iIntros "H". iDestruct "H" as (HgetSlice') "H".
      simpl. iFrame. eauto.
  Qed.

  (* TODO: this lemma is in the Coq standard library in master but not 8.9 *)
  Lemma skipn_firstn_comm' {A} (m n : nat) (l : Datatypes.list A):
    drop m (take n l) = take (n - m) (drop m l).
  Proof.
    revert n l. induction m; intros [] []; rewrite ?skipn_O -?minus_n_O ?take_nil //=.
  Qed.

  Lemma slice_skip_split {A} k data (bs0 bs: List.list A) q:
    k ≤ data.(slice.length) →
    data ↦{q} (bs0, bs)
         -∗ (slice.skip k data) ↦{q} (bs0, drop k bs)
         ∗ ((slice.skip k data) ↦{q} (bs0, drop k bs) -∗ data ↦{q} (bs0, bs)).
  Proof.
    iIntros (Hlen) "H". iDestruct "H" as (HgetSlice) "H".
    iSplitL "H".
    * iFrame.
      iPureIntro. move: HgetSlice. rewrite /Data.getSliceModel//=.
      rewrite /sublist_lookup/mguard/option_guard.
      destruct decide_rel; last by inversion 1.
      destruct decide_rel; last by lia.
      inversion 1. subst. f_equal.
      rewrite skipn_firstn_comm' drop_drop //.
    * iIntros "H". iDestruct "H" as (HgetSlice') "H".
      simpl. iFrame. eauto.
  Qed.

  Lemma wp_writeBuf f data inode bs0 bs1 bs2 q:
    {{{ f ↦ (inode, Write) ∗ inode ↦ bs1 ∗ data ↦{q} (bs0, bs2) }}}
      writeBuf f data
    {{{ RET tt; f ↦ (inode, Write) ∗ inode ↦ (bs1 ++ bs2) ∗ data ↦{q} (bs0, bs2) }}}.
  Proof.
    rewrite /writeBuf.
    rewrite -MAX_WRITE_LEN_unfold.
    iIntros (Φ) "(Hf&Hinode&Hdata) HΦ".
    iLöb as "IH" forall (data bs1 bs2 q).
    wp_loop.
    destruct compare_to.
    - wp_bind.
      iAssert (⌜ length bs2 < MAX_WRITE_LEN ⌝)%I with "[-]" as "%".
      { iDestruct "Hdata" as "(%&?)".
        iPureIntro. erewrite getSliceModel_len_inv; eauto. }
      iApply (wp_append with "[$]"); first by lia.
      iIntros "!> H". do 2 wp_ret. by iApply "HΦ".
    - wp_bind.
      iDestruct (slice_take_split MAX_WRITE_LEN with "Hdata") as "(Htake&Hwand)"; first by lia.
      iApply (wp_append with "[$]").
      { rewrite take_length. lia. }
      iIntros "!> (Hf&Hinode&Hdata)".
      iDestruct ("Hwand" with "Hdata") as "Hdata".
      wp_ret.
      iDestruct (slice_skip_split MAX_WRITE_LEN with "Hdata") as "(Hdrop&Hwand)"; first by lia.
      iApply ("IH" with "Hf Hinode Hdrop [HΦ Hwand]").
      iIntros "!> (Hf&Hinode&Hdata)".
      iDestruct ("Hwand" with "Hdata") as "Hdata".
      iApply "HΦ". iFrame. rewrite -app_assoc take_drop //.
  Qed.

  Definition readMessage_handle f :=
  (fileContents <- Data.newPtr (slice.t byte);
  initData <- Data.newSlice byte 0;
  _ <- Loop (fun pf =>
        buf <- FS.readAt f pf.(partialFile.off) 512;
        newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
        if compare_to Lt (slice.length buf) 512
        then
          _ <- Data.writePtr fileContents newData;
          LoopRet tt
        else
          Continue {| partialFile.off := pf.(partialFile.off) + slice.length buf;
                      partialFile.data := newData; |}) {| partialFile.off := 0;
           partialFile.data := initData; |};
  fileData <- Data.readPtr fileContents;
  fileStr <- Data.bytesToString fileData;
  _ <- FS.close f;
  Ret fileStr)%proc.

  (* TODO: this is no longer an equality, but the two programs are equivalent up
  to monad laws *)
  Lemma readMessage_unfold_open userDir name:
    readMessage userDir name =
    (let! f <- FS.open userDir name;
      readMessage_handle f)%proc.
  Proof. auto. Qed.
  Opaque readMessage.

  Lemma take_length_lt {A} (l : Datatypes.list A) (n : nat):
    length (take n l) < n → take n l = l.
  Proof.
    intros Hlen. apply take_ge.
    rewrite take_length in Hlen.
    lia.
  Qed.

  Lemma wp_readMessage_handle f inode ls q2 :
    {{{ f ↦ (inode, Read) ∗ inode ↦{q2} ls }}}
      readMessage_handle f
    {{{ RET (bytes_to_string ls); inode ↦{q2} ls }}}.
  Proof.
    rewrite /readMessage_handle.
    generalize 512 => k.
    iIntros (Φ) "(Hf&Hinode) HΦ".
    wp_bind.
    iApply (wp_newAlloc with "[//]").
    iIntros (fileContents) "!> HfC".
    wp_bind.
    iApply (@wp_newSlice with "[//]").
    iIntros (fileSlice) "!> HfS".
    simpl repeat.
    replace [] with (take 0 ls) by auto.
    generalize 0 => idx.
    wp_bind.
    iAssert (fileSlice ↦ take idx ls)%I with "[HfS]" as "HfS".
    { iExists _; eauto. }
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
      iApply (wp_bytesToString' with "HfS").
      iIntros "!> _".
      wp_bind.
      iApply (wp_close with "Hf").
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

  Lemma writeTmp_unfold_writeBuf msg:
    writeTmp msg =
    (let! (f, name) <- createTmp;
     _ <- writeBuf f msg;
     _ <- close f; Ret name)%proc.
  Proof. trivial. Qed.
  Opaque writeTmp.

  Global Instance ghost_init_status_inhabited :
    Inhabited (ghost_init_status).
  Proof. econstructor. exact Uninit. Qed.

  Lemma userRange_in_elim s k:
    userRange_ok s →
    k ∈ s →
    k < NumUsers.
  Proof.
    rewrite /userRange_ok => Hrange ?.
    destruct (lt_dec k NumUsers) as [?|Hn]; auto.
    assert (k ≥ NumUsers) by lia. exfalso; eapply Hrange; eauto.
  Qed.

  Lemma nth_error_snoc {A: Type} (l: List.list A) (a: A):
    nth_error (l ++ [a]) (length l) = Some a.
  Proof. induction l => //=. Qed.

  Lemma nth_error_snoc_ne {A: Type} (l: List.list A) (a: A) k:
    k ≠ length l →
    nth_error (l ++ [a]) k = nth_error l k.
  Proof.
    intros Hneq.
    destruct (lt_dec k (length l)) as [?|Hgt].
    - rewrite nth_error_app1 //.
    - assert (length l < k) by lia.
      etransitivity.
      * eapply nth_error_None. rewrite app_length //=. lia.
      * symmetry. eapply nth_error_None. lia.
  Qed.

  Lemma open_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} :
    {{{ j ⤇ K (Call Open) ∗ Registered ∗ ExecInv }}}
      MailServer.Open
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ γ) "(#Hsource&#Hinv)".
    rewrite /MailServer.Open.
    wp_bind.
    (* Take out the ghost variables needed to create the locks *)
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iDestruct "Hmsgs" as (ls) "(Hglobal&>Hrootdir&Hinit&Hm)".
    iDestruct (RootDirInv_range_ok with "Hrootdir") as %Hrange_ok.
    iDestruct "Hinit" as (init_stat) "Hinit".
    iMod (open_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)".
    { solve_ndisj. }
    (* Prove that the init status ghost variable must be Uninit
       by showing alternatives imply undefined behavior/false *)
    destruct init_stat; swap 1 3.
    { iDestruct "Hinit" as ">(?&%)".
      exfalso. congruence. }
    { iDestruct "Hinit" as ">(?&Hj'&%)".
      iMod (open_open_step_inv with "Hj Hj' [$] [$]").
      { solve_ndisj. }
      eauto. }
    iDestruct "Hinit" as ">(Hauth&Hfrag&%&Hghosts)".
    iApply wp_newAlloc; first by auto.
    iIntros (locks0) "!> Hlocks0".
    iExists _. iFrame.
    iExists _. iFrame.
    iMod (ghost_var_update (A := ghost_init_statusC) with "[$] [$]") as "(Hauth&Hfrag)".
    iSplitL "Hauth Hj".
    { iExists (Started_Init _ _). iFrame. eauto. }
    iModIntro.
    wp_bind.
    iApply @wp_newSlice; first by auto.
    iIntros (locks) "!> Hlocks".
    wp_bind.
    iApply (wp_writePtr with "[$]").
    iIntros "!> Hlocks0".
    simpl repeat.
    wp_bind.
    remember (@nil LockRef) as lock_list eqn:Heq_lock_list.
    replace 0 with (length lock_list) at 1; last first.
    { rewrite Heq_lock_list //. }
    iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
    iAssert ([∗ set] k ∈ dom (gset _) σ.(messages),
             ∃ γuid : gname, ⌜Γ !! k = Some γuid⌝ ∗
             match nth_error lock_list k with
             | Some lk => is_lock boxN lk (InboxLockInv γuid) True
             | None => InboxLockInv γuid 0
             end)%I with "[Hghosts]" as "Hghosts".
    { iApply big_sepS_mono; last auto.
      iIntros (k Hin) "H".
      iDestruct "H" as (γuid) "(Heq&Hlock)".
      iExists _; iFrame. rewrite Heq_lock_list.
      destruct k; auto.
    }
    assert (Hlen: length lock_list <= NumUsers) by
        (rewrite Heq_lock_list; cbn [length]; lia).
    clear Heq_lock_list.
    iLöb as "IH" forall (lock_list locks Hlen).
    wp_loop.
    destruct equal.
    - iClear "IH".
      wp_ret. wp_ret.
      iIntros "!>".
      wp_bind. iApply (wp_readPtr with "[$]").
      iIntros "!> Hlocks0".
      iInv "Hinv" as "H".
      iDestruct "H" as (σ') "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iDestruct "Hmsgs" as (ls') "(Hglobal&>Hrootdir&Hinit&Hm)".
      iDestruct (RootDirInv_range_ok with "Hrootdir") as %Hrange_ok'.
      iDestruct "Hinit" as (init_stat) "Hinit".
      iDestruct "Hinit" as "(>Hauth&Hinit)".
      iDestruct (ghost_var_agree (A := ghost_init_statusC) with "Hauth Hfrag") as %Heq.
      subst.
      iDestruct "Hinit" as ">(Hj&Hopen')".
      iDestruct "Hopen'" as %Hopen'.
      rewrite Hopen'. simpl GlobalInv. iDestruct "Hglobal" as ">Hglobal".
      iApply (wp_setX with "[$]").
      iIntros "!> Hglobal".
      rewrite (userRange_ok_eq _ _ Hrange_ok Hrange_ok').
      iAssert ([∗ set] k ∈ dom (gset uint64) σ'.(messages),
               ∃ γuid lk, ⌜Γ !! k = Some γuid⌝ ∗ ⌜ lock_list !! k = Some lk ⌝
                                  ∗ is_lock boxN lk (InboxLockInv γuid) True)%I
        with "[Hghosts]" as "Hghosts".
      { iApply big_sepS_mono; last eauto.
        iIntros (k Hin) "H".
        iDestruct "H" as (γuid Heq) "H".
        iExists γuid.
        destruct nth_error as [lk|] eqn:Heq_nth_error; last first.
        { exfalso. rewrite nth_error_None in Heq_nth_error *. eapply userRange_in_elim in Hin; auto.
          rewrite e. lia. }
        iExists lk. iSplitL ""; auto. iSplitL ""; auto.
        iPureIntro. rewrite -nth_error_lookup //.
      }
      iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. do 2 eexists; split.
        { rewrite /reads Hopen'. eauto. }
        do 2 econstructor; split; econstructor.
      }
      { solve_ndisj. }
      iExists _. iFrame. iExists lock_list. iFrame.
      iSplitR "Hj HΦ Hreg"; last first.
      { iModIntro. iApply "HΦ"; iFrame. }
      iExists _, O. iFrame.
      iMod (ghost_var_update (A := ghost_init_statusC) with "Hauth Hfrag") as "(Hauth&Hfrag)".
      iSplitL "Hrootdir".
      { iModIntro. rewrite /RootDirInv. simpl.
        rewrite dom_fmap_L //; eauto.
      }
      iSplitL "Hauth".
      { iExists Finished_Init. iFrame. eauto. }
      iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
      iDestruct (big_sepM_sep with "[Hm Hghosts]") as "Hm".
      { iFrame. }
      iModIntro. iNext.
      rewrite big_sepM_fmap.
      iApply big_sepM_mono; iFrame.
      iIntros (k (mstat&msgs) Hin) "(H1&H2)".
      iDestruct "H1" as (γ' lk' ? ?) "H".
      simpl. iDestruct "H2" as (?? _ _ _) "((Hinterp&?)&?&Hin)".
      iExists _, _.
      rewrite nth_error_lookup.
      iSplitL ""; auto.
      iSplitL ""; auto.
      iFrame.
    - wp_bind. iApply (wp_readPtr with "[$]").
      iIntros "!> Hlocks0".
      wp_bind.
      assert (length lock_list ∈ dom (gset uint64) σ.(messages)).
      { eapply Hrange_ok. move: Hlen n. rewrite /NumUsers.
        inversion 1; eauto.
        * congruence.
        * subst. lia.
      }
      iDestruct (big_sepS_delete with "Hghosts") as "(Huid&Hghosts)".
      { eauto. }
      iDestruct "Huid" as (γuid Heq_γuid) "Hlockinv".
      assert (nth_error lock_list (length lock_list) = None) as ->.
      { apply nth_error_None. trivial. }
      iApply (wp_newLock boxN _ _ (InboxLockInv γuid) True%I with "[Hlockinv]").
      { iFrame. iSplitL "".
        - iModIntro. by iIntros (i) "$".
        - iModIntro. by iIntros (i) "(?&$)".
      }
      iIntros (lk) "!> #His_lock".
      wp_bind.
      iApply (wp_sliceAppend with "[$]").
      iIntros (locks') "!> Hlocks'".
      wp_bind.
      iApply (wp_writePtr with "[$]").
      iIntros "!> Hlocks0".
      wp_ret.
      replace (length (lock_list) + 1) with (length (lock_list ++ [lk])); last first.
      { rewrite app_length //=. }
      iApply ("IH" with "[] [$] [$] [$] [$] [$] [Hghosts]").
      { iPureIntro. rewrite app_length //=. inversion Hlen; eauto.
        * congruence.
        * subst. rewrite /NumUsers. lia.
      }
      iApply (big_sepS_delete with "[Hghosts]").
      { eauto. }
      { iSplitL "".
        - iExists γuid. iSplitL ""; auto.
          rewrite nth_error_snoc //.
        - iApply (big_sepS_mono with "Hghosts").
          iIntros (k Hin) "H".
          iDestruct "H" as (γuid' ?) "H".
          iExists γuid'. iSplitL ""; auto.
          rewrite nth_error_snoc_ne; eauto.
          set_solver.
      }
  Qed.


  (* TODO: this actually only depends on TmpInv. For modulariy, maybe break up proof
     into a "re-usable" temp directory pattern? *)
  Lemma wp_createTmp Γ γ:
    {{{ inv execN (∃ σ : l.(OpState), source_state σ ∗ MsgsInv Γ γ σ ∗ HeapInv σ ∗ TmpInv) }}}
      createTmp
    {{{ (f: File) name (inode: Inode), RET (f, name);
        name ↦ inode ∗ inode ↦ [] ∗ f ↦ (inode, Write) }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    rewrite /createTmp.
    wp_bind.
    iApply wp_randomUint64; first auto.
    iIntros (id) "!> _".
    wp_bind.
    iApply wp_newAlloc; first auto.
    iIntros (finalName) "!> HfinalName".
    simpl repeat.
    wp_bind.
    iApply wp_newAlloc; first auto.
    iIntros (finalFile) "!> HfinalFile".
    wp_bind.
    iLöb as "IH" forall (id).
    wp_loop.
    wp_bind.
    rewrite /ExecInv.
    iFastInv "Hinv" "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iDestruct "Htmp" as (tmps_map) "(Hspool&Hspool_unlocked&Htmp_auth&Htmps)".
    destruct (decide (gmodel.(@uint64_to_string) id ∈ dom (gset string) tmps_map)) as
        [ Hin | Hfresh ].
    * iApply (wp_create_not_new with "[Hspool]").
      { iFrame. eauto. }
      iIntros (?) "!> Hspool".
      iExists _. iFrame. iExists _. iFrame.
      iModIntro. wp_bind.
      iApply wp_randomUint64; first auto.
      iIntros (id') "!> _". wp_ret.
      iNext. iApply ("IH" with "HΦ [$] [$]").
    * iApply (wp_create_new with "[Hspool]").
      { iFrame. eauto. }
      iIntros (inode f) "!> (Hf&Hinode&Hspool&Hpath)".
      iMod (gen_heap_alloc tmps_map (gmodel.(@uint64_to_string) id) inode with "Htmp_auth")
        as "(Htmp_auth&Htmp_frag)".
      { eapply not_elem_of_dom; eauto. }
      iExists _. iFrame.
      iPoseProof (big_sepM_insert_2 with "[Hpath] Htmps") as "Htmps".
      { iApply "Hpath". }
      iExists _. iFrame.
      rewrite dom_insert_L comm_L. iFrame.
      iModIntro.
      wp_bind.
      iApply (wp_writePtr with "HfinalName").
      iIntros "!> HfinalName".
      wp_bind.
      iApply (wp_writePtr with "HfinalFile").
      iIntros "!> HfinalFile".
      wp_ret. iNext. wp_ret.
      wp_bind.
      iApply (wp_readPtr with "HfinalName").
      iIntros "!> HfinalName".
      wp_bind.
      iApply (wp_readPtr with "HfinalFile").
      iIntros "!> _". wp_ret. iApply "HΦ"; by iFrame.

      Grab Existential Variables.
      (* TODO: this should not be necessary *)
      all: typeclasses eauto.
  Qed.

  Lemma TmpInv_path_acc name inode:
    name ↦ inode -∗ TmpInv -∗ (name ↦ inode ∗ path.mk SpoolDir name ↦ inode
                                    ∗ (path.mk SpoolDir name ↦ inode -∗ TmpInv )).
  Proof.
    iIntros "Hn Htmp".
    rewrite /TmpInv.
    iDestruct "Htmp" as (tmp_map) "(?&?&Htmp_auth&Hpaths)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Hlookup.
    iDestruct (@big_sepM_lookup_acc with "[$]") as "(Hpath&Hpaths)"; eauto.
    iFrame. iIntros. iExists _. iFrame. by iApply "Hpaths".
  Qed.

  Lemma MailboxStatusInterp_insert uid lk γ mstat mbox name body :
    mbox !! name = None →
    MailboxStatusInterp uid lk γ mstat mbox true
                        -∗ MailboxStatusInterp uid lk γ mstat (<[ name := body ]>mbox) true.
  Proof.
    iIntros (Hfresh) "Hinterp".
    destruct mstat; auto.
    iDestruct "Hinterp" as "($&HS)". iDestruct "HS" as (S) "(Hauth&%)".
    iExists _; iFrame. iPureIntro.
    etransitivity; first eauto.
    apply insert_subseteq; eauto.
  Qed.

  Lemma TmpInv_path_delete name inode:
    name ↦ inode -∗ TmpInv -∗
         |==> (∃ (S: gset string), path.mk SpoolDir name ↦ inode ∗ SpoolDir ↦ S
                 ∗ SpoolDir ↦ Unlocked
                 ∗ (SpoolDir ↦ (S ∖ {[ name ]}) -∗ SpoolDir ↦ Unlocked -∗ TmpInv )).
  Proof.
    iIntros "Hn Htmp".
    rewrite /TmpInv.
    iDestruct "Htmp" as (tmp_map) "(?&?&Htmp_auth&Hpaths)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Hlookup.
    iMod (@gen_heap_dealloc with "[$] [$]") as "Htmp_auth".
    iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto.
    iExists _. iFrame.
    iIntros "!> ??".
    iExists (map_delete name tmp_map).
    rewrite dom_delete_L. iFrame.
  Qed.

  Lemma InitInv_open_update Γ γ σ σ':
    σ.(open) = true →
    σ'.(open) = true →
    InitInv Γ γ σ -∗ InitInv Γ γ σ'.
  Proof.
    iIntros (Ho1 Ho2) "H".
    iDestruct "H" as (v) "(?&H)".
    destruct v.
    - iDestruct "H" as "(?&%&?)". congruence.
    - iDestruct "H" as "(?&%)". congruence.
    - rewrite /InitInv. iExists (Finished_Init). eauto.
  Qed.

  Lemma deliver_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg:
    {{{ j ⤇ K ((deliver uid msg)) ∗ Registered ∗ ExecInv }}}
      MailServer.Deliver uid msg
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ γinit) "(#Hsource&#Hinv)".
    wp_bind. wp_ret.
    rewrite -fupd_wp.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    rewrite /deliver.
    iMod (deliver_start_step_inv_do j (λ x, K (Bind x (λ x, Call (Deliver_End uid msg))))
            with "Hj Hsource Hstate")
          as (s alloc vs s' Heq) "(Hj&Hstate)".
    { solve_ndisj. }
    iMod (ghost_step_bind_ret with "Hj Hsource") as "Hj".
    { solve_ndisj. }
    destruct Heq as (Heq1&Heq2&Heq3).
    iExists _. iFrame.
    rewrite /HeapInv.
    iDestruct (big_sepDM_insert_acc (dec := sigPtr_eq_dec) with "[Hheap]")
      as "H"; eauto.
    { rewrite /Data.getAlloc in Heq1. eapply Heq1. }
    iDestruct "H" as "((Hp&%)&Hheap)".
    iAssert (▷ HeapInv (RecordSet.set heap
                          (RecordSet.set Data.allocs (updDyn msg.(slice.ptr) (s', alloc))) σ)
               ∗ msg.(slice.ptr) ↦{-1} alloc)%I
      with "[Hp Hheap]"
      as "($&Hp)".
    { destruct s; inversion Heq3.
      * simpl. iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
        iSplitR ""; last eauto.
        iApply "Hheap"; eauto.
      * simpl. iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
        iSplitR ""; last eauto.
        iApply "Hheap"; eauto.
    }
    iModIntro.
    iModIntro.
    rewrite writeTmp_unfold_writeBuf.
    wp_bind.
    wp_bind.
    iApply (wp_createTmp with "Hinv").
    iIntros (f name inode) "!> (Hghost&Hinode&Hf)".
    wp_bind.
    iApply (wp_writeBuf with "[Hf Hinode Hp]").
    { iFrame. eauto. }
    iIntros "!> (Hf&Hinode&Hp)".
    wp_bind.
    iApply (wp_close with "[$]").
    iIntros "!> _".
    wp_ret.
    rewrite app_nil_l.

    (* Link loop *)
    wp_bind.
    iApply wp_randomUint64; first auto.
    iIntros (id) "!> _".
    wp_bind.
    iLöb as "IH" forall (id).
    wp_loop.
    wp_bind.
    iInv "Hinv" as "H".
    clear σ Heq1 Heq2 Heq3.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    iMod (deliver_end_step_inv j K
            with "Hj Hsource Hstate")
          as ((mstat&mbox) msg_stat' alloc' vs' lstatus Heq) "(Hj&Hstate)".
    { solve_ndisj. }
    destruct Heq as (He1&Heq2&Heq3&Heq4).
    rewrite /MsgsInv. rewrite Hopen.
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hrootdir&Hinit&Hm)".
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk γ) "(>%&>%&#Hlock&Hinbox)".
    iDestruct "Hinbox" as "(Hmbox&>Hdircontents&Hmsgs)".
    iDestruct (TmpInv_path_acc with "[$] [$]") as "(Hghost&Hpath&Htmp)".
    (* Case on whether the file already exists *)
    destruct (decide (("msg" ++ uint64_to_string id)%string ∈ dom (gset string) mbox))
             as [Hin|Hfresh].
    - iApply (wp_link_not_new with "[Hpath Hdircontents]").
      { iFrame. eauto. }
      iIntros "!> (Hpath&Hdircontents)".
      iDestruct ("Htmp" with "Hpath") as "Htmp".
      iDestruct ("Hm" with "[Hmsgs Hmbox Hdircontents]") as "Hm".
      { iExists _, _. iFrame; eauto. }
      rewrite insert_id; last eauto.
      iExists _. iFrame.
      rewrite Hopen.
      iExists _. iFrame.
      iModIntro.
      wp_bind.
      iApply wp_randomUint64; first auto.
      iIntros (id') "!> _".
      wp_ret. iNext.
      iApply ("IH" with "[$] [$] [$] [$] [$] [$]").
    - iClear "IH".
      iApply (wp_link_new with "[Hpath Hdircontents]").
      { iFrame. eauto. }
      iIntros "!> (Hpath&Hpathnew&Hdircontents)".
      iDestruct ("Htmp" with "Hpath") as "Htmp".
      iDestruct (big_sepM_insert_2 with "[Hpathnew Hinode] Hmsgs") as "Hmsgs".
      { simpl. iExists inode, 0. iFrame. }
      iDestruct ("Hm" $! (mstat, <[ ("msg" ++ (uint64_to_string) id)%string := vs]> mbox)
                   with "[Hmsgs Hmbox Hdircontents]") as "Hm".
      { iExists _, _. iFrame.
        rewrite dom_insert_L comm_L. iFrame.
        iFrame "Hlock".
        iSplitL ""; first eauto.
        iSplitL ""; first eauto.
        simpl.
        iApply MailboxStatusInterp_insert; eauto.
        eapply not_elem_of_dom; eauto.
      }
      iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. apply opened_step; auto. econstructor.
        eexists. split.
        - rewrite /lookup/readSome. rewrite He1. eauto.
        - do 2 eexists; split.
          { econstructor; eauto. eapply not_elem_of_dom; eauto. }
          do 2 eexists; split.
          { rewrite /readUnlockSlice.
            do 2 eexists; split.
            { rewrite /readSome Heq2 //. }
            do 2 eexists; split.
            { rewrite /readSome Heq4 //. }
            do 2 eexists; split.
            { econstructor. }
            { rewrite /readSome Heq3 //. }
          }
          econstructor.
      }
      { solve_ndisj. }
      iDestruct (HeapInv_agree_slice with "[$] [$]") as %(?&?); eauto.
      subst.
      iExists _. iFrame.
      iSplitL "Hheap Hm Hglobal Hp Hrootdir Hinit".
      {
        iExists _. iFrame.
        simpl open. rewrite Hopen. iFrame.
        iDestruct (big_sepDM_insert_acc _ _ (msg.(slice.ptr)) Heq2 (dec := sigPtr_eq_dec) with "[Hheap]")
          as "H"; eauto.
        iDestruct "H" as "((Hlookup&%)&Hclose)".
        iDestruct (InitInv_open_update with "[$]") as "$"; auto.
        iSplitL "Hrootdir".
        { iModIntro. rewrite /RootDirInv. simpl.
          rewrite dom_insert_L_in //; eauto.
          { eapply elem_of_dom. eexists; eauto. }
        }
        iApply "Hclose".
        iSplitR ""; auto.
        iModIntro.
        destruct msg_stat'; inversion Heq4; [].
        simpl.
        iDestruct "Hp" as (??) "Hp".
        iDestruct (Count_Typed_Heap.read_split_join with "[$]") as "H".
        destruct num; inv_step; eauto.
      }
      wp_ret.
      wp_ret.
      iModIntro. iNext.
      (* Delete the temp file *)
      rewrite /delete.
      iInv "Hinv" as "H".
      iDestruct "H" as (?) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iMod (TmpInv_path_delete with "[$] Htmp") as (S) "(Hpath&Hdir&Hdirlock&Hwand)".
      iApply (wp_delete with "[$]").
      iIntros "!> (?&?)".
      iDestruct ("Hwand" with "[$] [$]") as "Htmp".
      iExists _. iFrame.
      iApply "HΦ". by iFrame.

      Grab Existential Variables.
      all: typeclasses eauto.
  Qed.

  Lemma delete_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg:
    {{{ j ⤇ K (Call (Delete uid msg)) ∗ Registered ∗ ExecInv }}}
      MailServer.Delete uid msg
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ γinit) "(#Hsource&#Hinv)".
    wp_bind. wp_ret.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hrootdir&Hinit&Hm)".
    iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
    iDestruct "Hread" as (lsptr) "(Hglobal_read&Hlsptr)".
    iMod (delete_step_inv with "Hj Hsource Hstate") as (v body (Heq1&Heq2)) "(Hj&Hstate)".
    { solve_ndisj. }
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk γ) "(>%&>%&#Hlock&>Hinbox)".
    iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
    iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
    { intros. econstructor. eexists; split; last by econstructor.
      econstructor; eauto. eapply opened_step; auto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq1. eauto.
      - simpl. do 2 eexists; split.
        * rewrite Heq2 //=.
        * econstructor.
    }
    { solve_ndisj. }
    iDestruct (big_sepM_delete with "Hmsgs") as "(Hcurr_msg&Hmsgs)"; eauto.
    iDestruct "Hmbox" as "(Hlocked&Hlockinv&Hdirlock)".
    iDestruct "Hcurr_msg" as (inode q) "(Hpath&Hinode)".
    iApply (wp_delete with "[Hpath Hdircontents Hdirlock]").
    { iFrame. }
    iIntros "!> (Hdircontents&Hdirlock)".
    iExists _. iFrame. iModIntro.
    iSplitR "HΦ Hreg Hj".
    - iNext. iExists _. iFrame.
      simpl open. rewrite Hopen. iFrame.
      iDestruct (InitInv_open_update with "[$]") as "$"; auto.
      iSplitL "Hrootdir".
      { rewrite /RootDirInv //=. rewrite dom_insert_L_in //.
        eapply elem_of_dom. eauto.
      }
      iApply "Hm". iExists _, _. iFrame.
      do 2 (iSplitL ""; eauto).
      iFrame "Hlock".
      rewrite dom_delete_L. iFrame.
    - iApply "HΦ". iFrame.
  Qed.

  Lemma lock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid:
    {{{ j ⤇ K (Call (Lock uid)) ∗ Registered ∗ ExecInv }}}
      MailServer.Lock uid
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ γinit) "(#Hsource&#Hinv)".
    wp_bind.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hrootdir&Hinit&Hm)".
    iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
    iDestruct "Hread" as (lsptr) "(Hglobal_read&Hlsptr)".
    iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read".
    iMod (lock_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
    { solve_ndisj. }
    iDestruct (MsgsInv_pers_split with "Hm") as "#Huid"; first eauto.
    iDestruct "Huid" as (lk γ HΓlookup Hnth) "#Hlock".

    (* re-do invariant *)
    iExists _. iFrame. iExists _. rewrite Hopen. iFrame.

    iModIntro.
    wp_bind. iApply (wp_sliceRead with "[$]").
    { eauto. }
    iIntros "!> Hlsptr".

    (* We need to simulate the step *after* the lock acquisition. So we
       need to allow a view shift in the post-condition with the following: *)
    iApply wp_fupd.

    iApply (wp_lockAcquire_writer with "Hlock").
    { set_solver+. }
    iIntros "!> (Hlockinv&Hlocked)".

    iInv "Hinv" as "H".
    clear σ Hopen Heq v.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls') "(>Hglobal&Hrootdir&Hinit&Hm)".
    iMod (lock_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
    { solve_ndisj. }

    iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk' γ') "(>Heq1&>Heq2&Hinbox)".
    iDestruct "Heq1" as %Heq1.
    iDestruct "Heq2" as %Heq2.
    iDestruct "Hinbox" as "(_&Hmbox&Hdircontents&Hmsgs)".
    assert (lk' = lk) by congruence. subst.
    assert (γ' = γ) by congruence. subst.
    iDestruct "Hmbox" as "[>Hmbox|Hmbox]"; last first.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S ?) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
    }



    iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
    { intros. econstructor. eexists; split; last by econstructor.
      econstructor; eauto. eapply opened_step; auto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq. eauto.
      - simpl. do 2 eexists; split; constructor.
    }
    { solve_ndisj. }

    iExists _. iFrame. simpl open. rewrite Hopen.
    iSplitR "Hj HΦ Hreg".
    { iModIntro. iNext.
      iExists _. iFrame.
      iSplitL "Hrootdir".
      { rewrite /RootDirInv //=. rewrite dom_insert_L_in //.
        eapply elem_of_dom. eauto.
      }
      iSplitL "Hinit".
      { iApply InitInv_open_update; eauto. }
      iApply "Hm".
      rewrite /MsgInv. iExists _, _.
      iSplitL ""; first by done.
      iSplitL ""; first by done.
      rewrite /InboxInv. by iFrame.
    }
    iModIntro. iModIntro. iApply "HΦ". by iFrame.
  Qed.

  Lemma unlock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid:
    {{{ j ⤇ K (Call (Unlock uid)) ∗ Registered ∗ ExecInv }}}
      MailServer.Unlock uid
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ γinit) "(#Hsource&#Hinv)".
    wp_bind.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hrootdir&Hinit&Hm)".
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
      econstructor; eauto. eapply opened_step; auto. econstructor.
      eexists. split.
      - rewrite /lookup/readSome. rewrite Heq. eauto.
      - simpl. do 2 eexists; split; econstructor.
    }
    { solve_ndisj. }
    iExists _. iFrame.
    iExists _.
    simpl open. rewrite Hopen. iFrame.
    iDestruct "Hmbox" as "(Hwlock&Hlockinv&Hunlocked)".
    iSplitL "Hm Hmsgs Hdircontents Hunlocked Hrootdir Hinit".
    { iModIntro.  iNext.
      iDestruct (InitInv_open_update with "[$]") as "$"; auto.
      iSplitL "Hrootdir".
      { rewrite /RootDirInv//=. rewrite dom_insert_L_in; eauto.
        eapply elem_of_dom; eauto. }
      iApply "Hm". iExists _, _.
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
    iDestruct "Hrest" as (Γ γinit) "(#Hsource&#Hinv)".
    wp_bind.
    iInv "Hinv" as "H".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv' with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls) "(>Hglobal&Hrootdir&Hinit&Hm)".
    iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
    iDestruct "Hread" as (lsptr) "(Hglobal_read&Hlsptr)".
    iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read".
    iMod (pickup_step_inv with "[$] [$] [$]") as ((v&Heq)) "(Hj&Hstate)".
    { solve_ndisj. }
    iDestruct (MsgsInv_pers_split with "Hm") as "#Huid"; first eauto.
    iDestruct "Huid" as (lk γ HΓlookup Hnth) "#Hlock".

    (* re-do invariant *)
    iExists _. iFrame. iExists _. rewrite Hopen. iFrame.

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
    clear σ Hopen Heq v.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv' with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls') "(>Hglobal&Hrootdir&Hinit&Hm)".
    iMod (pickup_step_inv with "[$] [$] [$]") as ((v&Heq)) "(Hj&Hstate)".
    { solve_ndisj. }

    iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
    iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk' γ') "(>Heq1&>Heq2&Hinbox)".
    iDestruct "Heq1" as %Heq1.
    iDestruct "Heq2" as %Heq2.
    iDestruct "Hinbox" as "(_&Hmbox&Hdircontents&Hmsgs)".
    assert (lk' = lk) by congruence. subst.
    assert (γ' = γ) by congruence. subst.
    destruct v as (status&msgs).
    destruct status.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S) "(Hauth&%)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
    }
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
      iDestruct "Hauth" as (S ?) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
    }
    iDestruct "Hmbox" as "[>Hmbox|Hmbox]"; last first.
    { iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
      iDestruct "Hauth" as (S ?) "(Hauth&?)".
      iExFalso.
      iDestruct "Hlockinv" as (S' ?) "(Hauth'&?)".
      iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
    }

    iApply (wp_list_start with "Hmbox").
    iIntros "!> Hmbox".
    iModIntro.
    iExists _. iFrame.
    iExists _. iFrame.
    replace 0%Z with (O: Z) by auto.
    iPoseProof (@Count_Heap.read_split_join1 with "Hmbox") as "(Hrl&Hmbox)".
    rewrite ?Hopen. iFrame.
    iSplitL "Hm Hmbox Hdircontents Hmsgs Hlockinv".
    { iNext.
      iApply "Hm". iExists _, _. iFrame "%".
      iFrame "Hlock". iFrame.
      iRight. iFrame.
    }


    iInv "Hinv" as "H".
    clear σ Hopen Heq Heq1 Heq2 msgs.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iMod (is_opened_step_inv' with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    { solve_ndisj. }
    rewrite /MsgsInv ?Hopen.
    iDestruct "Hmsgs" as (ls') "(>Hglobal&Hrootdir&Hinit&Hm)".
    iMod (pickup_step_inv with "[$] [$] [$]") as ((v&Heq)) "(Hj&Hstate)".
    { solve_ndisj. }

    iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
    iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto.
    iDestruct "Huid" as (lk' γ') "(>Heq1&>Heq2&Hinbox)".
    iDestruct "Heq1" as %Heq1.
    iDestruct "Heq2" as %Heq2.
    iDestruct "Hinbox" as "(_&Hmbox&>Hdircontents&Hmsgs)".
    assert (lk' = lk) by congruence. subst.
    assert (γ' = γ) by congruence. subst.
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
        econstructor; eauto. eapply opened_step; auto. econstructor.
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
    iExists _. simpl open. rewrite Hopen. iFrame.
    replace 0%Z with (O: Z) by auto.

    iSplitL "Hm Hlocked Hcontents_auth Hdircontents Hmsgs Hrootdir Hinit".
    { iNext.
      iDestruct (InitInv_open_update with "[$]") as "$"; auto.
      iSplitL "Hrootdir".
      { rewrite /RootDirInv dom_insert_L_in //.
        { eapply elem_of_dom; eauto. }
      }
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
    iIntros (messages') "!> Hmessages".
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
      clear σ Hopen Heq.
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iMod (pickup_end_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
      { simpl; auto. }
      { solve_ndisj. }
      rewrite /MsgsInv ?Hopen.
      iDestruct "Hmsgs" as (ls') "(>Hglobal&Hopen&Hinit&Hm)".
      iDestruct (GlobalInv_unify with "[$] [$] [$]") as %<-.
      iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto.
      iDestruct "Huid" as (lk' γ') "(>Heq1&>Heq2&Hinbox)".
      iDestruct "Heq1" as %Heq1'.
      iDestruct "Heq2" as %Heq2'.
      iDestruct "Hinbox" as "(Hlock'&Hmbox&>Hdircontents&>Hmsgs)".
      assert (lk' = lk) by congruence. subst.
      assert (γ' = γ) by congruence. subst.
      iDestruct "Hmbox" as ">(Hwlock&Hlockinv)".
      iDestruct "Hlockinv" as (S) "(Hauth&Hsubset)".
      iDestruct "Hsubset" as %Hsubset.
      iDestruct (ghost_var_agree (A := contentsC) with "Hauth Hcontents_frag") as %?.
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
      iExists _. iFrame. rewrite ?Hopen. iFrame.
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
      iIntros "!> Hinode".
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
      clear σ Hopen Heq.
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      (* Show messages' ptr can't be in σ, else we'd have a redundant pts to *)
      iDestruct (slice_mapsto_non_null with "[Hmessages]") as %?.
      { iExists _; eauto. }
      iDestruct (HeapInv_non_alloc_inv _ _ 0 with "[$] [Hmessages]") as %?; first auto.
      { iDestruct "Hmessages" as "(?&?)"; iFrame. }
      iMod (pickup_end_step_inv with "Hj Hsource Hstate") as (v Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
      { simpl; auto. }
      { solve_ndisj. }
      iDestruct "Hmessages" as (malloc Hmalloc) "Hmessages".
      iMod (ghost_step_call _ _ _ messages'
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. apply opened_step; auto. econstructor.
        do 2 eexists.
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
      iExists _. iFrame. simpl open. rewrite Hopen.
      iSplitR "Hj Hmessages0 HΦ Hreg".
      { iModIntro. iNext.
        iSplitL "Hmsgs Hcontents_frag Hdirlock".
        { simpl. rewrite /MsgsInv. iDestruct "Hmsgs" as (l0) "(?&Hrootdir&Hinit&Hmap)".
          iExists _. iFrame.
          simpl.
          iDestruct (InitInv_open_update with "[$]") as "$"; auto.
          iSplitL "Hrootdir".
          { rewrite /RootDirInv//= dom_insert_L_in //.
            eapply elem_of_dom; eauto.
          }
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
        iFrame; eauto.
      }
      iModIntro. wp_bind.
      iApply (wp_readPtr with "[$]").
      iIntros "!> Hptr". wp_ret. iApply "HΦ". iFrame.
  Time Qed.


End refinement_triples.
