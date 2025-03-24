From iris.proofmode Require Import environments.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG:heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.
Section protocol.
Record RWMutex_protocol_names :=
  {
    read_wait_gn : gname;
    rlock_overflow_gn : gname;
    wlock_gn : gname;
    writer_sem_tok_gn : gname;
    state_gn : gname;
  }.

Implicit Types γ : RWMutex_protocol_names.
Local Definition own_RWMutex_invariant γ (writer_sem reader_sem reader_count reader_wait : w32)
  (state : rwmutex) : iProp Σ :=
  ∃ wl (pos_reader_count : w32) outstanding_reader_wait,
    "Houtstanding" ∷ own_tok_auth γ.(read_wait_gn) outstanding_reader_wait ∗
    "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2) wl ∗
    "Hrlock_overflow" ∷ own_tok_auth γ.(rlock_overflow_gn) (Z.to_nat sync.rwmutexMaxReaders) ∗
    "Hrlocks" ∷ own_toks γ.(rlock_overflow_gn) (Z.to_nat (1 + sint.Z pos_reader_count)) ∗
    "%Hpos_reader_count_pos" ∷ ⌜ 0 ≤ sint.Z pos_reader_count < sync.rwmutexMaxReaders ⌝ ∗

    "%Hreader_count" ∷
      ⌜ match wl with
      | NotLocked _ => reader_count = pos_reader_count
      | _ => reader_count = word.sub pos_reader_count (W32 sync.rwmutexMaxReaders)
      end ⌝ ∗

    match state with
    | RLocked num_readers =>
        "%Hnum_readers_le" ∷ ⌜ (Z.of_nat num_readers + uint.Z reader_sem ≤ sint.Z pos_reader_count)%Z ⌝
    | _ => "_" ∷ emp
    end ∗

    match wl with
    | SignalingReaders _
    | WaitingForReaders =>
        "_" ∷ True
    | _ => "%Houtstanding_zero" ∷ ⌜ outstanding_reader_wait = O ⌝
    end ∗

    match wl with
    | WaitingForReaders => "_" ∷ True
    | _ => "Hwriter_unused" ∷ ghost_var γ.(writer_sem_tok_gn) 1 ()
    end ∗

    match wl, state with
    | NotLocked unnotified_readers, RLocked num_readers =>
        "%Hfast" ∷
          (⌜ reader_wait = W32 0 ∧ writer_sem = W32 0 ∧
           sint.Z pos_reader_count = (Z.of_nat num_readers + sint.Z unnotified_readers + uint.Z reader_sem)%Z ⌝)
    | SignalingReaders remaining_readers, RLocked num_readers =>
        "%Hblocked_unsignaled" ∷
        ⌜ 0 ≤ sint.Z remaining_readers < sync.rwmutexMaxReaders ∧
          sint.Z reader_wait ≤ 0 ∧
          (Z.of_nat outstanding_reader_wait + Z.of_nat num_readers + uint.Z reader_sem =
           sint.Z remaining_readers + sint.Z reader_wait)%Z ∧
           writer_sem = W32 0 ⌝
    | WaitingForReaders, RLocked num_readers =>
        "Hwriter" ∷ (ghost_var γ.(writer_sem_tok_gn) 1 () ∨
                     ghost_var γ.(writer_sem_tok_gn) (1/2) () ∗ ⌜ writer_sem = W32 0 ∧ reader_wait = W32 0 ⌝) ∗
        "%Hblocked" ∷
        ⌜ Z.of_nat outstanding_reader_wait + Z.of_nat num_readers + uint.Z reader_sem ≤ sint.Z reader_wait ∧
          (writer_sem = W32 0 ∨ (writer_sem = W32 1 ∧ reader_wait = W32 0)) ⌝
    | IsLocked, Locked =>
        "%Hlocked" ∷
        ⌜ writer_sem = W32 0 ∧ reader_wait = W32 0 ∧ reader_sem = W32 0 ⌝
    | _, _ => False
    end.
#[global] Opaque own_RWMutex_invariant.
#[local] Transparent own_RWMutex_invariant.

#[global] Instance own_RWMutex_invariant_timeless a b c d e f : Timeless (own_RWMutex_invariant a b c d e f) := _.

Local Ltac rwauto :=
  solve [repeat first [eexists || intuition || subst || done || split ||
                               simplify_eq || destruct decide || unfold sync.rwmutexMaxReaders in * || word ]].

Lemma step_RLock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait state :
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  if decide (0 ≤ (sint.Z (word.add reader_count (W32 1)))) then
    ∃ num_readers,
      "%" ∷ ⌜ state = RLocked num_readers ⌝ ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait (RLocked (S num_readers))
  else
    "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait state.
Proof.
  iIntros "[Hrlock Hinv]". iNamed "Hinv". iModIntro.
  iCombine "Hrlock Hrlocks" as "Hrlocks".
  iCombine "Hrlock_overflow Hrlocks" gives %Hoverflow.
  destruct state, wl; iNamed "Hinv"; try done.
  { destruct decide; last (exfalso; rwauto).
    iExists _; iSplitR; first done. iFrame. iFrame. iExists (word.add pos_reader_count (W32 1)).
    iSplitL "Hrlocks". { iApply to_named. iExactEq "Hrlocks". f_equal. rwauto. }
    iPureIntro. rwauto. }
  all: destruct decide; [exfalso; rwauto| ];
    iFrame; iFrame; iExists (word.add pos_reader_count (W32 1));
    iSplitL "Hrlocks"; [iApply to_named; iExactEq "Hrlocks"; f_equal; rwauto| ];
    iPureIntro; rwauto.
Qed.

Lemma step_RLock_readerSem_Semacquire γ writer_sem reader_sem reader_count reader_wait state :
  0 < uint.Z reader_sem →
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  ∃ num_readers,
    "%" ∷ ⌜ state = RLocked num_readers ⌝ ∗
    "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem (word.sub reader_sem (W32 1)) reader_count reader_wait (RLocked (S num_readers)).
Proof.
  iIntros "%Hsem_acq Hinv". iNamed "Hinv". destruct state, wl; iNamed "Hinv"; try done.
  1-3: try (iExists _; iSplitR; first done); iFrame; iFrame; iPureIntro; rwauto.
  { rwauto. }
Qed.

Lemma step_TryRLock_readerCount_CompareAndSwap γ writer_sem reader_sem reader_count reader_wait state :
  0 ≤ sint.Z reader_count →
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  ∃ num_readers,
    "%" ∷ ⌜ state = RLocked num_readers ⌝ ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait
    (RLocked (S num_readers)).
Proof.
  iIntros "%Hpos [Hrlock Hinv]". iNamed "Hinv". iModIntro.
  iCombine "Hrlock Hrlocks" as "Hrlocks".
  iCombine "Hrlock_overflow Hrlocks" gives %Hoverflow.
  destruct state, wl; iNamed "Hinv"; try done.
  2-4: exfalso; rwauto.
  iFrame. iFrame. iExists _; iSplitR; first done.
  iExists (word.add pos_reader_count (W32 1)). iFrame.
  iSplitL "Hrlocks". { iApply to_named. iExactEq "Hrlocks". f_equal. rwauto. }
  iPureIntro. rwauto.
Qed.

Lemma step_RUnlock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait num_readers :
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait (RLocked (S num_readers)) ==∗
  "Hrtok" ∷ own_toks γ.(rlock_overflow_gn) 1 ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 (-1))) reader_wait (RLocked num_readers) ∗
  if decide (sint.Z (word.add reader_count (W32 (-1))) < sint.Z 0) then
    "Hwait_tok" ∷ own_toks γ.(read_wait_gn) 1 ∗
    "%" ∷ ⌜ sint.Z reader_count ≠ sint.Z 0 ⌝ ∗
    "%" ∷ ⌜ sint.Z reader_count ≠ -sint.Z sync.rwmutexMaxReaders ⌝
  else True.
Proof.
  iIntros "Hinv". iNamed "Hinv".
  replace (Z.to_nat (1 + _))%nat with (1 + Z.to_nat (1 + sint.Z (word.sub pos_reader_count (W32 1))))%nat by word.
  iDestruct (own_toks_plus with "Hrlocks") as "[Hr Hrlocks]".
  destruct wl; iNamed "Hinv"; try done.
  - destruct decide. { exfalso. rwauto. } iFrame. iFrame. iPureIntro. rwauto.
  - destruct decide.
    * iMod (own_tok_auth_plus 1 with "Houtstanding") as "[Houtstanding $]".
      iFrame. iFrame. iPureIntro. rwauto.
    * exfalso. rwauto.
  - destruct decide.
    * iMod (own_tok_auth_plus 1 with "Houtstanding") as "[Houtstanding $]".
      iFrame. iFrame. iPureIntro. rwauto.
    * exfalso. rwauto.
Qed.

Lemma step_rUnlockSlow_readerWait_Add γ writer_sem reader_sem reader_count reader_wait state :
  own_toks γ.(read_wait_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait (W32 (-1))) state ∗
  if decide (word.add reader_wait (W32 (-1)) = W32 0) then
    "Hwtok" ∷ ghost_var γ.(writer_sem_tok_gn) (1/2) ()
  else "_" ∷ True.
Proof.
  iIntros "[Hwait_tok Hinv]". iNamed "Hinv".
  iCombine "Houtstanding Hwait_tok" gives %Hle.
  destruct state, wl; iNamed "Hinv"; try done.
  - rwauto.
  - destruct outstanding_reader_wait; first rwauto.
    iMod (own_tok_auth_delete_S with "Houtstanding [$]") as "Houtstanding".
    iFrame.
    destruct decide.
    * exfalso. rwauto.
    * iFrame. iPureIntro. rwauto.
  - destruct outstanding_reader_wait; first rwauto.
    iMod (own_tok_auth_delete_S with "Houtstanding [$]") as "Houtstanding".
    iModIntro. iFrame.
    iDestruct "Hwriter" as "[[Hwriter Hwriter2]|[_ %Hbad]]".
    2:{ exfalso. rwauto. }
    destruct decide.
    * iSplitR "Hwriter2"; last by iFrame.
      repeat (iSplitR; first by iPureIntro; rwauto).
      iSplitL. { iRight. iFrame. iPureIntro. rwauto. }
      iPureIntro. rwauto.
    * iFrame. iPureIntro. rwauto.
  - rwauto.
Qed.

Lemma step_rUnlockSlow_writerSem_Semrelease γ writer_sem reader_sem reader_count reader_wait state :
  ghost_var γ.(writer_sem_tok_gn) (1/2) () ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ (word.add writer_sem (W32 1)) reader_sem reader_count reader_wait state.
Proof.
  iIntros "[Hwriter_tok Hinv]". iNamed "Hinv". iModIntro.
  destruct state, wl; iNamed "Hinv"; try done.
  all: try (iCombine "Hwriter_unused Hwriter_tok" gives %[Hbad _]; done).
  iDestruct "Hwriter" as "[Hbad | [Hwriter %]]".
  { iCombine "Hbad Hwriter_tok" gives %[Hbad _]; done. }
  iCombine "Hwriter Hwriter_tok" as "Hwriter".
  iFrame. iFrame. iPureIntro.
  intuition; subst.
  { right. rwauto. }
  { right. rwauto. }
Qed.

Lemma step_Lock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait state :
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (W32 0)) ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  (if decide (reader_count = W32 0) then
     "%" ∷ ⌜ state = RLocked 0 ⌝ ∗
     "Hwl_inv" ∷ ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
     "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem
       (word.add reader_count (W32 (-sync.rwmutexMaxReaders))) reader_wait Locked
   else
     "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2)
      (SignalingReaders (word.add (word.add reader_count (W32 (-sync.rwmutexMaxReaders)))
                           (W32 sync.rwmutexMaxReaders))) ∗
     "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem
       (word.add reader_count (W32 (-sync.rwmutexMaxReaders))) reader_wait state).
Proof.
  iIntros "[Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  destruct decide.
  - iMod (ghost_var_update_2 IsLocked with "Hwl Hwl_in") as "[Hwl Hwl_in]".
    { apply Qp.half_half. }
    destruct num_readers.
    2:{ exfalso. rwauto. }
    iModIntro. iSplitR; first done.
    iFrame. iPureIntro. rwauto.
  - iMod (ghost_var_update_2 (SignalingReaders _) with "Hwl Hwl_in") as "[Hwl Hwl_in]".
    { apply Qp.half_half. }
    iFrame. iPureIntro. rwauto.
Qed.

Lemma step_Lock_readerWait_Add γ r writer_sem reader_sem reader_count reader_wait state :
  ghost_var γ.(wlock_gn) (1/2) (SignalingReaders r) ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  if decide (sint.Z (word.add reader_wait r) = sint.Z 0) then
     "%" ∷ ⌜ state = RLocked 0 ⌝ ∗
     "Hwl_inv" ∷ ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
    "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait r) Locked
  else
    "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2) WaitingForReaders ∗
    "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait r) state.
Proof.
  iIntros "[Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  injection H as ->.
  destruct decide.
  - iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
    { apply Qp.half_half. }
    iFrame. iPureIntro. destruct num_readers; rwauto.
  - iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
    { apply Qp.half_half. }
    iFrame. iPureIntro. rwauto.
Qed.

Lemma step_Lock_writerSem_Semacquire γ writer_sem reader_sem reader_count reader_wait state :
  0 < uint.Z writer_sem →
  ghost_var γ.(wlock_gn) (1/2) WaitingForReaders ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  "%" ∷ ⌜ state = RLocked 0 ⌝ ∗
  "Hwl_inv" ∷ ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ (word.sub writer_sem (W32 1)) reader_sem reader_count reader_wait Locked.
Proof.
  iIntros "%Hsem [Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  destruct num_readers. 2:{ exfalso. rwauto. }
  iSplitR; first done. iModIntro.
  iFrame. iDestruct "Hwriter" as "[?|[_ %]]".
  2:{ exfalso. rwauto. }
  iFrame. iPureIntro. rwauto.
Qed.

Lemma step_TryLock_readerCount_CompareAndSwap γ writer_sem reader_sem reader_count reader_wait state :
  sint.Z reader_count = sint.Z 0 →
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (W32 0)) ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  "%" ∷ ⌜ state = RLocked 0 ⌝ ∗
  "Hwl_inv" ∷ ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 (-sync.rwmutexMaxReaders)))
    reader_wait Locked.
Proof.
  iIntros "%Hz [Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  iFrame. iPureIntro. destruct num_readers; rwauto.
Qed.

Lemma step_Unlock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait :
  ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait Locked ==∗
  "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2) (NotLocked (word.add reader_count (W32 sync.rwmutexMaxReaders))) ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 sync.rwmutexMaxReaders)) reader_wait (RLocked 0) ∗
  "%" ∷ ⌜ 0 ≤ sint.Z (word.add reader_count (W32 sync.rwmutexMaxReaders)) ⌝ ∗
  "%" ∷ ⌜ sint.Z (word.add reader_count (W32 sync.rwmutexMaxReaders)) < sint.Z sync.rwmutexMaxReaders ⌝.
Proof.
  iIntros "[Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  iFrame. iPureIntro. rwauto.
Qed.

Lemma step_Unlock_readerSem_Semrelease γ writer_sem reader_sem reader_count reader_wait r state :
  0 < sint.Z r →
  ghost_var γ.(wlock_gn) (1/2) (NotLocked r) ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2) (NotLocked (word.sub r (W32 1))) ∗
  "Hprot_inv" ∷ own_RWMutex_invariant γ writer_sem (word.add reader_sem (W32 1))reader_count reader_wait state.
Proof.
  iIntros "%Hpos [Hwl_in Hinv]". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  iFrame. iPureIntro. rwauto.
Qed.
End protocol.

Section wps.
Record RWMutex_names :=
  {
    prot_gn : RWMutex_protocol_names;
    reader_sem_gn : gname;
    writer_sem_gn : gname;
  }.
Implicit Types γ : RWMutex_names.

Definition own_RWMutex γ (state : rwmutex) : iProp Σ :=
  ghost_var γ.(prot_gn).(state_gn) (1/2) state.
#[global] Opaque own_RWMutex.
#[local] Transparent own_RWMutex.

Definition own_RLock_token γ : iProp Σ :=
  own_toks γ.(prot_gn).(rlock_overflow_gn) 1.
#[global] Opaque own_RLock_token.
#[local] Transparent own_RLock_token.

(* FIXME: add hints like this to named prop *)
Hint Extern 100 (Timeless (?n ∷ ?P)) =>
       (change (n ∷ P) with P) : typeclass_instances.

Definition is_RWMutex (rw : loc) γ N : iProp Σ :=
  "#Hmu" ∷ is_Mutex (struct.field_ref_f sync.RWMutex "w" rw) (ghost_var γ.(prot_gn).(wlock_gn) (1/2) (NotLocked (W32 0))) ∗
  "#His_readerSem" ∷ is_sema (struct.field_ref_f sync.RWMutex "readerSem" rw) γ.(reader_sem_gn) (N.@"sema") ∗
  "#His_writerSem" ∷ is_sema (struct.field_ref_f sync.RWMutex "writerSem" rw) γ.(writer_sem_gn) (N.@"sema") ∗
  "#Hinv" ∷ inv (N.@"inv") (
      ∃ writer_sem reader_sem reader_count reader_wait state,
        "Hstate" ∷ ghost_var γ.(prot_gn).(state_gn) (1/2) state ∗
        "HreaderSem" ∷ own_sema γ.(reader_sem_gn) reader_sem ∗
        "HwriterSem" ∷ own_sema γ.(writer_sem_gn) writer_sem ∗
        "HreaderCount" ∷ own_Int32 (struct.field_ref_f sync.RWMutex "readerCount" rw) (DfracOwn 1)
          reader_count ∗
        "HreaderWait" ∷ own_Int32 (struct.field_ref_f sync.RWMutex "readerWait" rw) (DfracOwn 1)
          reader_wait ∗
        "Hprot" ∷ own_RWMutex_invariant γ.(prot_gn) writer_sem reader_sem reader_count reader_wait state ∗
        "Hlocked" ∷ (match state with
                     | Locked => own_Mutex (struct.field_ref_f sync.RWMutex "w" rw) ∗
                                ghost_var γ.(prot_gn).(wlock_gn) (1/2) IsLocked
                     | _ => True
                     end
          )
    ).
#[global] Opaque is_RWMutex.
#[local] Transparent is_RWMutex.
Instance is_RWMutex_pers rw γ N : Persistent (is_RWMutex rw γ N) := _.

Import Ltac2.
Set Default Proof Mode "Classic".

Tactic Notation "runInPure" tactic(x) :=
  lazymatch goal with
  | [ |- envs_entails (Envs _ ?es _) _ ] => idtac
  | [ |- _ ] => x
  end.

Ltac rwInvStart := iInv "Hinv" as ">Hi" "Hclose"; iNamedSuffix "Hi" "_inv".
Ltac rwInvEnd := iCombineNamed "*_inv" as "Hi"; iMod ("Hclose" with "[Hi]") as "_";
                   [iNamed "Hi"; solve [repeat iFrame] | ]; iModIntro.
Ltac rwStep x :=
  iMod (x with "[$]") as "Hprot_inv";
  (runInPure word); []; try destruct decide; iNamed "Hprot_inv".

Ltac rwLinearizeStart :=
  iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj];
  try (iDestruct "HΦ" as (?) "HΦ"); iDestruct "HΦ" as "[Hstate HΦ]";
  iCombine "Hstate Hstate_inv" gives %[_ ?]; simplify_eq;
  iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate2_inv Hstate_inv]"; first apply Qp.half_half;
  try iModIntro.
Ltac rwLinearizeEnd :=
  first [ iMod ("HΦ" with "[$]") as "HΦ" |
          iMod ("HΦ" with "[//] [$]") as "HΦ" ]; iMod "Hmask" as "_".
Ltac rwLinearize := rwLinearizeStart; rwLinearizeEnd.

Ltac rwAtomicStart := iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
Ltac rwAtomicEnd := iMod "Hmask" as "_".

Lemma wp_RWMutex__RLock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ -∗
  (|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
     (∀ num_readers, ⌜ state = RLocked num_readers ⌝ → own_RWMutex γ (RLocked (S num_readers)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "RLock" #() {{ Φ }}.
Proof.
  wp_start as "[#His Htok]". iNamed "His". wp_auto.
  wp_apply wp_Int32__Add.
  rwInvStart.
  rwStep step_RLock_readerCount_Add.
  - (* fast path *)
    rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd. rwLinearize. rwInvEnd.
    wp_auto. rewrite -> bool_decide_false by word. wp_auto. iApply "HΦ".
  - (* slow path *)
    rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd. rwInvEnd.
    wp_auto. rewrite -> bool_decide_true by word. wp_auto.
    wp_apply wp_runtime_SemacquireRWMutexR; first iFrame "#".
    rwInvStart. rwAtomicStart. iFrame. iIntros "% H1_inv". rwAtomicEnd.
    rwStep step_RLock_readerSem_Semacquire. rwLinearize. rwInvEnd. wp_auto. iFrame.
Qed.

Lemma wp_RWMutex__TryRLock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ -∗
  ((|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
      (∀ num_readers, ⌜ state = RLocked num_readers ⌝ →
                      own_RWMutex γ (RLocked (S num_readers)) ={∅,⊤∖↑N}=∗ Φ #true)) ∧
   Φ #false)
  -∗
  WP rw @ sync @ "RWMutex'ptr" @ "TryRLock" #() {{ Φ }}.
Proof.
  wp_start as "[#His Htok]". iNamed "His". wp_auto.
  wp_for. wp_apply wp_Int32__Load.
  rwInvStart. iFrame. rwAtomicStart. iIntros "H1_inv". rwAtomicEnd. rwInvEnd.
  wp_auto. rewrite bool_decide_decide. destruct decide.
  - (* failed to get RLock *)
    wp_auto. wp_for_post. iRight in "HΦ". iFrame.
  - (* try doing a CAS *)
    wp_auto. wp_apply wp_Int32__CompareAndSwap. rwInvStart. rwAtomicStart.
    iFrame. destruct decide.
    * (* CAS successful *)
      iSplitR; first done. iIntros "H1_inv".
      rwStep step_TryRLock_readerCount_CompareAndSwap.
      rwAtomicEnd. iLeft in "HΦ". rwLinearize. rwInvEnd.
      rewrite bool_decide_true //. wp_auto. wp_for_post. iFrame.
    * (* CAS failed *)
      iSplitR; first done. iIntros "H1_inv". rwAtomicEnd. rwInvEnd.
      rewrite bool_decide_false //. wp_auto. wp_for_post. iFrame.
Qed.

Lemma wp_RWMutex__RUnlock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N -∗
  (|={⊤∖↑N,∅}=> ∃ num_readers,
     own_RWMutex γ (RLocked (S num_readers)) ∗
     (own_RWMutex γ (RLocked num_readers) ∗ own_RLock_token γ ={∅,⊤∖↑N}=∗
      Φ #())) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "RUnlock" #() {{ Φ }}.
Proof.
  wp_start as "#His". iNamed "His". wp_auto.
  wp_apply wp_Int32__Add.
  rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd.
  rwLinearizeStart.
  rwStep step_RUnlock_readerCount_Add; rwLinearizeEnd; rwInvEnd.
  - (* decrease number of readers Lock() is waiting for *)
    wp_auto. rewrite bool_decide_true //. wp_auto.
    wp_method_call. wp_call. iClear "rw r". clear r_ptr rw_ptr.
    wp_auto. rewrite bool_decide_decide. destruct decide. { exfalso. word. }
    wp_auto. rewrite bool_decide_decide. destruct decide. { exfalso. word. }
    wp_auto. wp_apply wp_Int32__Add.
    rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd.
    rwStep step_rUnlockSlow_readerWait_Add; rwInvEnd.
    * (* wake up Lock() *)
      wp_auto. rewrite bool_decide_true //. wp_auto. wp_apply wp_runtime_Semrelease.
      { iFrame "#". }
      rwInvStart. rwStep step_rUnlockSlow_writerSem_Semrelease.
      rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd. rwInvEnd.
      wp_auto. iFrame.
    * wp_auto. rewrite bool_decide_false //. wp_auto. iFrame.
  - wp_auto. rewrite bool_decide_false //. wp_auto. iFrame.
Qed.

Lemma wp_RWMutex__Lock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N -∗
  (|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
     (⌜ state = RLocked 0 ⌝ → own_RWMutex γ Locked ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "Lock" #() {{ Φ }}.
Proof.
  wp_start as "His". iNamed "His". wp_auto.
  wp_apply wp_Mutex__Lock.
  { iFrame "#". }
  iIntros "[Hlocked Hwl]". wp_auto.
  wp_apply wp_Int32__Add.
  rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd.
  rwStep step_Lock_readerCount_Add.
  - (* fast path *)
    rwLinearize. iRename "Hlocked" into "Hlocked2_inv". rwInvEnd.
    wp_auto. iFrame.
  - (* slow path *)
    rwInvEnd. wp_auto. rewrite bool_decide_false.
    2:{ intros H. word. } (* FIXME: word. *)
    wp_auto. wp_apply wp_Int32__Add.
    rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd.
    rwStep step_Lock_readerWait_Add.
    * (* got lock now, no need to Semacquire *)
      rwLinearize. iRename "Hlocked" into "Hlocked2_inv". rwInvEnd.
      wp_auto. rewrite -> bool_decide_true by word. wp_auto. iFrame.
    * (* Wait for remaining readers *)
      rwInvEnd. wp_auto. rewrite -> bool_decide_false.
      2:{ intros ?. word. } (* FIXME: word *)
      wp_auto. wp_apply wp_runtime_SemacquireRWMutex.
      { iFrame "#". }
      rwInvStart. rwAtomicStart. iFrame. iIntros "%Hpos H1_inv". rwAtomicEnd.
      rwStep step_Lock_writerSem_Semacquire.
      rwLinearize. iRename "Hlocked" into "Hlocked2_inv". rwInvEnd.
      wp_auto. iFrame.
Qed.

Lemma wp_RWMutex__TryLock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N -∗
  ((|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
    (⌜ state = RLocked 0 ⌝ → own_RWMutex γ Locked ={∅,⊤∖↑N}=∗ Φ #true)) ∧
     Φ #false) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "TryLock" #() {{ Φ }}.
Proof.
  wp_start as "His". iNamed "His". wp_auto.
  wp_apply wp_Mutex__TryLock.
  { iFrame "#". }
  iIntros (?) "Hl".
  destruct locked.
  2:{ iRight in "HΦ". wp_auto. iFrame. }
  iDestruct "Hl" as "[Hlocked Hwl]".
  wp_auto.
  wp_apply wp_Int32__CompareAndSwap. rwInvStart.
  rwAtomicStart. iFrame. destruct decide.
  - iSplitR; first done. iIntros "H1_inv". rwAtomicEnd.
    rwStep step_TryLock_readerCount_CompareAndSwap.
    iLeft in "HΦ". rwLinearize. iRename "Hlocked" into "Hlocked2_inv". rwInvEnd.
    wp_auto. iFrame.
  - iSplitR; first done. iIntros "H1_inv". rwAtomicEnd. rwInvEnd.
    rewrite bool_decide_false //. wp_auto.
    wp_apply (wp_Mutex__Unlock with "[Hlocked Hwl]").
    { iFrame "#". iFrame. }
    iRight in "HΦ". iFrame.
Qed.

Lemma wp_RWMutex__Unlock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N -∗
  (|={⊤∖↑N,∅}=> own_RWMutex γ Locked ∗
    (own_RWMutex γ (RLocked 0) ={∅,⊤∖↑N}=∗ Φ #())
  ) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "Unlock" #() {{ Φ }}.
Proof.
  wp_start as "His". iNamed "His". wp_auto.
  wp_apply wp_Int32__Add.
  rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv". rwAtomicEnd.
  rwLinearize. iDestruct "Hlocked_inv" as "[Hlocked ?]". rwStep step_Unlock_readerCount_Add. rwInvEnd.
  wp_auto. rewrite bool_decide_decide. destruct decide.
  { exfalso. word. }
  wp_auto.
  set (r:=(word.add reader_count (W32 sync.rwmutexMaxReaders))) in *.
  iAssert (∃ (i : w64) r',
              "i" ∷ i_ptr ↦ i ∗
              "Hwl" ∷ ghost_var γ.(prot_gn).(wlock_gn) (1/2) (NotLocked r') ∗
              "%Hi" ∷ ⌜ sint.Z i ≤ sint.Z r ⌝ ∗
              "%Hr'" ∷ ⌜ sint.Z r' = sint.Z r - sint.Z i ⌝
          )%I with "[i Hwl]" as "Hloop".
  { iFrame. iPureIntro. word. }
  wp_for "Hloop". rewrite bool_decide_decide; destruct decide.
  - (* not done with loop *)
    wp_auto. wp_apply wp_runtime_Semrelease. { iFrame "#". }
    rwInvStart. rwAtomicStart. iFrame. iIntros "H1_inv".
    iMod (step_Unlock_readerSem_Semrelease with "[$]") as "Hprot_inv".
    {
      rewrite Hr'. clear dependent r'.
      enough (sint.Z (W64 (uint.Z r)) = sint.Z r) by word.
      clear -H H0.
      unfold W64.
      generalize dependent r. intros.
      rewrite !word.signed_of_Z.
      rewrite word.signed_eq_swrap_unsigned.
      rewrite word.signed_eq_swrap_unsigned in H H0.
      unfold word.swrap in *.
      unfold sync.rwmutexMaxReaders in H0.
      word.
      (* FIXME: word. *)
    }
    iNamed "Hprot_inv". rwAtomicEnd. rwInvEnd.
    wp_auto. wp_for_post.
    iFrame. iPureIntro. split.
    { assert (sint.Z (word.add i (W64 1)) = sint.Z i + 1) by word.
      rewrite H1. admit. (* FIXME: signed cast seems to be incorrect. *) }
    { word. }
  - wp_auto. replace (r') with (W32 0).
    2:{ admit. } (* FIXME: word. *)
    wp_apply (wp_Mutex__Unlock with "[Hlocked Hwl]").
    { iFrame "#". iFrame. }
    iFrame.
Admitted.

End wps.
End proof.
