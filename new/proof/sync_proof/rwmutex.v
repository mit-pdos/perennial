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
  own_toks γ.(rlock_overflow_gn) 1 -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  if decide (0 ≤ (sint.Z (word.add reader_count (W32 1)))) then
    ∃ num_readers,
      ⌜ state = RLocked num_readers ⌝ ∧
      own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait (RLocked (S num_readers))
  else
    own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait state.
Proof.
  iIntros "Hrlock Hinv". iNamed "Hinv".
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
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  ∃ num_readers,
    ⌜ state = RLocked num_readers ⌝ ∧
    own_RWMutex_invariant γ writer_sem (word.sub reader_sem (W32 1)) reader_count reader_wait (RLocked (S num_readers)).
Proof.
  iIntros "%Hsem_acq Hinv". iNamed "Hinv". destruct state, wl; iNamed "Hinv"; try done.
  1-3: try (iExists _; iSplitR; first done); iFrame; iFrame; iPureIntro; rwauto.
  { rwauto. }
Qed.

Lemma step_TryRLock_readerCount_CompareAndSwap γ writer_sem reader_sem reader_count reader_wait state :
  0 ≤ sint.Z reader_count →
  own_toks γ.(rlock_overflow_gn) 1 -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  ∃ num_readers,
    ⌜ state = RLocked num_readers ⌝ ∧
  own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait
    (RLocked (S num_readers)).
Proof.
  iIntros "%Hpos Hrlock Hinv". iNamed "Hinv".
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
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 (-1))) reader_wait (RLocked num_readers) ∗
  if decide (sint.Z (word.add reader_count (W32 (-1))) < sint.Z 0) then
    own_toks γ.(read_wait_gn) 1 ∗
    ⌜ sint.Z reader_count ≠ sint.Z 0 ⌝ ∗
    ⌜ sint.Z reader_count ≠ -sint.Z sync.rwmutexMaxReaders ⌝
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
  own_toks γ.(read_wait_gn) 1 -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait (W32 (-1))) state ∗
  if decide (word.add reader_wait (W32 (-1)) = W32 0) then
    ghost_var γ.(writer_sem_tok_gn) (1/2) ()
  else True.
Proof.
  iIntros "Hwait_tok Hinv". iNamed "Hinv".
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
  ghost_var γ.(writer_sem_tok_gn) (1/2) () -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  own_RWMutex_invariant γ (word.add writer_sem (W32 1)) reader_sem reader_count reader_wait state.
Proof.
  iIntros "Hwriter_tok Hinv". iNamed "Hinv".
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
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (W32 0)) -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  (if decide (reader_count = W32 0) then
     ⌜ state = RLocked 0 ⌝ ∗
     ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
     own_RWMutex_invariant γ writer_sem reader_sem
       (word.add reader_count (W32 (-sync.rwmutexMaxReaders))) reader_wait Locked
   else
     ghost_var γ.(wlock_gn) (1/2) (SignalingReaders reader_count) ∗
     own_RWMutex_invariant γ writer_sem reader_sem
       (word.add reader_count (W32 (-sync.rwmutexMaxReaders))) reader_wait state).
Proof.
  iIntros "Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
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
  ghost_var γ.(wlock_gn) (1/2) (SignalingReaders r) -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  if decide (sint.Z (word.add reader_wait r) = sint.Z 0) then
     ⌜ state = RLocked 0 ⌝ ∗
     ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
    own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait r) Locked
  else
    ghost_var γ.(wlock_gn) (1/2) WaitingForReaders ∗
    own_RWMutex_invariant γ writer_sem reader_sem reader_count (word.add reader_wait r) state.
Proof.
  iIntros "Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
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
  ghost_var γ.(wlock_gn) (1/2) WaitingForReaders -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  ⌜ state = RLocked 0 ⌝ ∗
  ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
  own_RWMutex_invariant γ (word.sub writer_sem (W32 1)) reader_sem reader_count reader_wait Locked.
Proof.
  iIntros "%Hsem Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
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
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (W32 0)) -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  ⌜ state = RLocked 0 ⌝ ∗
  ghost_var γ.(wlock_gn) (1/2) IsLocked ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 (-sync.rwmutexMaxReaders)))
    reader_wait Locked.
Proof.
  iIntros "%Hz Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl, state; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  iFrame. iPureIntro. destruct num_readers; rwauto.
Qed.

Lemma step_Unlock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait :
  ghost_var γ.(wlock_gn) (1/2) IsLocked -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait Locked ==∗
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (word.add reader_count (W32 sync.rwmutexMaxReaders))) ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 sync.rwmutexMaxReaders)) reader_wait (RLocked 0) ∗
  ⌜ 0 ≤ sint.Z (word.add reader_count (W32 sync.rwmutexMaxReaders)) ⌝.
Proof.
  iIntros "Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
  destruct wl; iNamed "Hinv"; try done.
  iMod (ghost_var_update_2 with "Hwl Hwl_in") as "[Hwl Hwl_in]".
  { apply Qp.half_half. }
  iFrame. iPureIntro. rwauto.
Qed.

Lemma step_Unlock_readerSem_Semrelease γ writer_sem reader_sem reader_count reader_wait r state :
  0 < sint.Z r →
  ghost_var γ.(wlock_gn) (1/2) (NotLocked r) -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  ghost_var γ.(wlock_gn) (1/2) (NotLocked (word.sub r (W32 1))) ∗
  own_RWMutex_invariant γ writer_sem (word.add reader_sem (W32 1))reader_count reader_wait state.
Proof.
  iIntros "%Hpos Hwl_in Hinv". iNamed "Hinv". iCombine "Hwl_in Hwl" gives %[_ ?].
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

Definition is_RWMutex (rw : loc) γ N : iProp Σ :=
  ∃ w,
  "#mu" ∷ rw ↦s[sync.RWMutex :: "w"]□ w ∗
  "#Hmu" ∷ is_Mutex w (ghost_var γ.(prot_gn).(wlock_gn) (1/2) (NotLocked (W32 0))) ∗
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
        "Hprot" ∷ own_RWMutex_invariant γ.(prot_gn) writer_sem reader_sem reader_count reader_wait state
    ).
#[global] Opaque is_RWMutex.
#[local] Transparent is_RWMutex.

Lemma wp_RWMutex__RLock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ -∗
  (|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
     (∀ num_readers, ⌜ state = RLocked num_readers ⌝ → own_RWMutex γ (RLocked (S num_readers)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "RLock" #() {{ Φ }}.
Proof.
  wp_start as "[#His Htok]". iNamed "His". wp_auto.
  wp_apply wp_Int32__Add.
  iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
  iDestruct (step_RLock_readerCount_Add with "[$] [$]") as "Hprot_inv".
  destruct decide.
  - (* fast path *)
    iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj].
    iFrame. iIntros "!> H1_inv". iDestruct "HΦ" as (?) "[Hstate HΦ]".
    iCombine "Hstate Hstate_inv" gives %[_ ?]. subst.
    iDestruct "Hprot_inv" as (?) "[% Hprot_inv]". simplify_eq.
    iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate Hstate_inv]"; first apply Qp.half_half.
    iMod ("HΦ" with "[//] Hstate") as "HΦ".
    iMod "Hmask". iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]"). { iNamed "Hi". iFrame. }
    iModIntro. wp_auto. rewrite bool_decide_decide decide_False //.
    2:{ word. }
    wp_auto. iApply "HΦ".
  - (* slow path *)
    iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
    iFrame. iIntros "H1_inv".
    iMod "Hmask" as "_". iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
    clear writer_sem reader_sem reader_wait.
    iModIntro. wp_auto. rewrite bool_decide_decide decide_True //.
    2:{ word. }
    wp_auto.
    wp_apply wp_runtime_SemacquireRWMutexR.
    { iFrame "#". }
    iInv "Hinv" as ">Hi" "Hclose".
    iNamedSuffix "Hi" "_inv".
    iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
    iFrame. iIntros "%Hpos H1_inv".
    iDestruct (step_RLock_readerSem_Semacquire with "[$]") as (?) "[%Heq Hprot_inv]"; first word.
    iMod "Hmask" as "_". subst.
    iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj].
    iDestruct "HΦ" as (?) "[Hstate HΦ]".
    iCombine "Hstate Hstate_inv" gives %[_ ?]. simplify_eq.
    iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate Hstate_inv]"; first apply Qp.half_half.
    iMod ("HΦ" with "[//] Hstate") as "HΦ".
    iMod "Hmask" as "_". iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
    iModIntro. wp_auto. iFrame.
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
  iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
  iFrame. iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
  iIntros "H1_inv". iMod "Hmask" as "_". iCombineNamed "*_inv" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
  iModIntro. wp_auto. rewrite bool_decide_decide. destruct decide.
  - (* failed to get RLock *)
    wp_auto. wp_for_post. iRight in "HΦ". iFrame.
  - (* try doing a CAS *)
    wp_auto.
    wp_apply wp_Int32__CompareAndSwap.
    iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
    iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
    iFrame. destruct decide.
    * (* CAS successful *)
      iSplitR; first done.
      iDestruct (step_TryRLock_readerCount_CompareAndSwap with "[$] [$]") as (?) "[% Hprot_inv]".
      { word. }
      subst. iIntros "H1_inv". iMod "Hmask" as "_". iLeft in "HΦ".
      iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj].
      iDestruct "HΦ" as (?) "[Hstate HΦ]".
      iCombine "Hstate Hstate_inv" gives %[_ ?]. simplify_eq.
      iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate Hstate_inv]"; first apply Qp.half_half.
      iMod ("HΦ" with "[//] Hstate") as "HΦ".
      iMod "Hmask" as "_". iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
      iModIntro. rewrite bool_decide_true //. wp_auto.
      wp_for_post. iFrame.
    * (* CAS failed *)
      iSplitR; first done. iIntros "H1_inv". iMod "Hmask" as "_".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
      iModIntro. rewrite bool_decide_false //. wp_auto.
      wp_for_post. iFrame.
Qed.

Lemma wp_RWMutex__RUnlock γ rw N :
  ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N -∗
  (|={⊤∖↑N,∅}=> ∃ num_readers,
     own_RWMutex γ (RLocked (S num_readers)) ∗
     (own_RWMutex γ (RLocked num_readers) -∗ own_RLock_token γ ={∅,⊤∖↑N}=∗
      Φ #())) -∗
  WP rw @ sync @ "RWMutex'ptr" @ "RUnlock" #() {{ Φ }}.
Proof.
  wp_start as "#His". iNamed "His". wp_auto.
  wp_apply wp_Int32__Add.
  iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
  iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
  iFrame. iIntros "H1_inv". iMod "Hmask" as "_".
  iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj].
  iDestruct "HΦ" as (?) "[Hstate HΦ]".
  iCombine "Hstate Hstate_inv" gives %[_ ?]. simplify_eq.
  iMod (step_RUnlock_readerCount_Add with "[$]") as "(Hrtok & Hprot_inv & Htok)".
  iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate Hstate_inv]"; first apply Qp.half_half.
  iMod ("HΦ" with "Hstate [$]"). iMod "Hmask" as "_".
  iCombineNamed "*_inv" as "Hi". iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
  iModIntro. wp_auto. rewrite bool_decide_decide. destruct decide.
  - (* decrease number of readers Lock() is waiting for *)
    wp_auto. wp_method_call. wp_call. iClear "rw r". clear r_ptr rw_ptr.
    wp_auto. iDestruct "Htok" as "(Htok & % & %)".
    rewrite bool_decide_decide. destruct decide.
    { exfalso. word. }
    wp_auto.
    rewrite bool_decide_decide. destruct decide.
    { exfalso. word. }
    wp_auto. wp_apply wp_Int32__Add.
    iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
    iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
    iFrame. iIntros "H1_inv". iMod "Hmask" as "_".
    iMod (step_rUnlockSlow_readerWait_Add with "[$] [$]") as "[Hprot_inv Htok]".
    iCombineNamed "*_inv" as "Hi". iMod ("Hclose" with "[Hi]") as "_". { iNamed "Hi". iFrame. }
    iModIntro. wp_auto. rewrite bool_decide_decide. destruct decide.
    * (* wake up Lock() *)
      wp_auto. wp_apply wp_runtime_Semrelease.
      { iFrame "#". }
      iInv "Hinv" as ">Hi" "Hclose". iNamedSuffix "Hi" "_inv".
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
      iFrame. iIntros "H1_inv". iMod "Hmask" as "_".
      iDestruct (step_rUnlockSlow_writerSem_Semrelease with "[$] [$]") as "Hprot_inv".
      iCombineNamed "*_inv" as "Hi". iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. } iModIntro. wp_auto. iFrame.
    * wp_auto. iFrame.
  - wp_auto. iFrame.
Qed.

End wps.
End proof.
