From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants ghost_map.
From Perennial.program_logic Require Import weakestpre.

Require Export New.code.sync.
From New.proof Require Import proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Import sync.atomic.
From New.proof Require Import tok_set.
From New.experiments Require Import glob.

From Perennial Require Import base.

Set Default Proof Using "Type".

Class syncG Σ := {
    #[global] wg_tokG :: tok_setG Σ;
    #[global] wg_totalG :: ghost_varG Σ w32
  }.

Definition syncΣ := #[tok_setΣ; ghost_varΣ w32].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance race_pkg_is_init : IsPkgInit race := ltac2:(build_pkg_init ()).

#[global]
Program Instance pkg_is_init : IsPkgInit sync := ltac2:(build_pkg_init ()).

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hinv" ∷ inv nroot (
        ∃ b : bool,
          (m ↦s[ sync.Mutex :: "state" ]{# 1/4} b) ∗
                  if b then True else
                    m ↦s[sync.Mutex :: "state"]{# 3/4} b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[sync.Mutex :: "state"]{# 3/4} true.

Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %[Hbad _].
  exfalso.
  rewrite go_type_size_unseal in Hbad. naive_solver.
  (* FIXME: don't want to unseal go_type_size_unseal *)
Qed.

Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_Mutex m).
Proof. apply _. Qed.

Lemma struct_val_aux_cons decls f t fvs :
  (struct.val_aux (structT $ (f,t) :: decls) fvs) =
  (default (zero_val t) (alist_lookup_f f fvs), (struct.val_aux (structT decls) fvs))%V.
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma struct_val_aux_nil fvs :
  (struct.val_aux (structT $ []) fvs) = #().
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma flatten_struct_tt :
  flatten_struct (# ()%V) = [].
Proof. rewrite to_val_unseal //=. Qed.

Theorem init_Mutex R E m : is_pkg_init sync -∗ m ↦ (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "#Hi Hl HR".
  simpl.
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".
  simpl.
  iFrame "#".
  iMod (inv_alloc nroot _ (_) with "[Hstate HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hstate".
    iDestruct "Hstate" as "[$$]".
  }
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    m @ sync @ "Mutex'ptr" @ "Lock" #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  wp_start as "H". iNamed "H".
  iLöb as "IH".
  wp_method_call. wp_call.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
    by iApply "IH".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    { done. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    m @ sync @ "Mutex'ptr" @ "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His & Hlocked & HR)".
  iNamed "His".
  wp_bind (CmpXchg _ _ _).
  iInv nroot as (b) "[>Hl _]".

  unfold own_Mutex.
  iCombine "Hl Hlocked" gives %[_ [=]]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
  { econstructor. }
  { econstructor. }
  iIntros "!# Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_auto; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

Definition is_Locker (i : interface.t) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} (interface.get #"Lock" #i) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} (interface.get #"Unlock" #i) #() {{{ RET #(); True }}})
.

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_Mutex m R -∗
  is_Locker (interface.mk sync "Mutex'ptr"%go #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#[? ?]".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_auto.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

Ltac simpl_word_constants :=
  repeat match goal with
         | [ H: context[word.unsigned (W64 ?x)] |- _ ] => change (uint.Z x) with x in H
         | [ |- context[word.unsigned (W64 ?x)] ] => change (uint.Z x) with x
         | [ H: context[word.unsigned (W32 ?x)] |- _ ] => change (uint.Z (W32 x)) with x in H
         | [ |- context[word.unsigned (W32 ?x)] ] => change (uint.Z (W32 x)) with x
         | [ H: context[word.unsigned (W8 ?x)] |- _ ] => change (uint.Z (W32 8)) with x in H
         | [ |- context[word.unsigned (W8 ?x)] ] => change (uint.Z (W8 x)) with x
         | [ H: context[word.signed (W64 ?x)] |- _ ] => change (sint.Z x) with x in H
         | [ |- context[word.signed (W64 ?x)] ] => change (sint.Z x) with x
         | [ H: context[word.signed (W32 ?x)] |- _ ] => change (sint.Z (W32 x)) with x in H
         | [ |- context[word.signed (W32 ?x)] ] => change (sint.Z (W32 x)) with x
         | [ H: context[word.signed (W8 ?x)] |- _ ] => change (sint.Z (W32 8)) with x in H
         | [ |- context[word.signed (W8 ?x)] ] => change (sint.Z (W8 x)) with x
        (* TODO: add sint versions *)
    end.

Ltac word_cleanup_core :=
  (* this is so that the following pattern succeeds when (for some reason)
  instead of w64 we have its unfolding *)
  fold w64 w32 w8 in *;
  repeat autounfold with word in *;
  try lazymatch goal with
      (* TODO: this isn't the right strategy if the numbers in the goal are used
      signed. [word] can try both via backtracking, but this can't be part of
      "cleanup".  *)
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      | |- not (@eq u64 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u32 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u8 _ _) => apply (f_not_equal uint.Z)
      end;
  simpl_word_constants;
  (* can't replace some of these with [autorewrite], probably because typeclass inference
  isn't the same *)
  repeat (
      rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
        ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
        ?word.unsigned_mul, ?w64_unsigned_ltu,
        ?word.signed_add, ?word.signed_sub in *
      || rewrite -> ?word.unsigned_of_Z, ?word.of_Z_unsigned in *
      || autorewrite with word in *
    );
  repeat match goal with
         | _ => progress simpl_word_constants
         | [ H: @eq w64 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_f_equal in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_f_equal in H as [H H']
         | [ H: not (@eq w64 _ _) |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_neq in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_neq in H as [H H']
         end;
  repeat match goal with
         | [ |- context[uint.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[uint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ |- context[sint.Z ?x] ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         | [ H: context[sint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite -> (@wrap_small _ word ok z) by lia
         | |- context[@word.swrap _ ?word ?ok ?z] =>
           rewrite -> (@swrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite -> (Z2Nat.id z) by lia
         end.

(* TODO: only for backwards compatibility.

[word_cleanup] should be be replaced with a new tactic
that does a subset of safe and useful rewrites *)
Ltac word_cleanup := word_cleanup_core; try lia.

Ltac word := first [
                 solve [
                     try iPureIntro;
                     word_cleanup_core;
                     unfold word.wrap in *;
                     unfold word.swrap in *;
                     (* NOTE: some inefficiency here because [lia] will do [zify]
                 again, but we can't rebind the zify hooks in Ltac *)
                     zify; Z.div_mod_to_equations; lia
                   ]
               | fail 1 "word could not solve goal"
               ].

Inductive rwmutex := RLocked (num_readers : nat) | Locked.

Inductive wlock_state :=
| NotLocked (unnotified_readers : nat)
| SignalingReaders (remaining_readers : nat)
| WaitingForReaders
| IsLocked.

Record RWMutex_names :=
  {
    read_wait_gn : gname;
    rlock_overflow_gn : gname;
    wlock_gn : gname;
  }.

Implicit Types γ : RWMutex_names.

Context `{!tok_setG Σ}.
Context `{!ghost_varG Σ wlock_state}.

Definition own_RWMutex_invariant γ (writer_sem reader_sem reader_count reader_wait : w32)
  (state : rwmutex) : iProp Σ :=
  ∃ wl (pos_reader_count : w32) outstanding_reader_wait,
    "Houtstanding" ∷ own_tok_auth γ.(read_wait_gn) outstanding_reader_wait ∗
    "Hwl" ∷ ghost_var γ.(wlock_gn) (1/2) wl ∗
    "Hrlock_overflow" ∷ own_tok_auth γ.(rlock_overflow_gn) (Z.to_nat sync.rwmutexMaxReaders) ∗
    "Hrlocks" ∷ own_toks γ.(rlock_overflow_gn) (S (Z.to_nat (sint.Z pos_reader_count))) ∗
    "%Hpos_reader_count_pos" ∷ ⌜ 0 ≤ sint.Z pos_reader_count ⌝ ∗

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
    | SignalingReaders _ | WaitingForReaders => "_" ∷ emp
    | _ => "%Houtstanding_zero" ∷ ⌜ outstanding_reader_wait = O ⌝
    end ∗

    match wl, state with
    | NotLocked unnotified_readers, RLocked num_readers =>
        "%Hfast" ∷
          (⌜ reader_wait = W32 0 ∧ writer_sem = W32 0 ∧
           sint.Z pos_reader_count = (Z.of_nat num_readers + sint.Z unnotified_readers + uint.Z reader_sem)%Z ⌝)
    | SignalingReaders remaining_readers, RLocked num_readers =>
        "%Hblocked_unsignaled" ∷
        ⌜ (Z.of_nat outstanding_reader_wait + Z.of_nat num_readers + uint.Z reader_sem = Z.of_nat remaining_readers + sint.Z reader_wait)%Z ∧
          reader_wait = W32 0 ∧ writer_sem = W32 0 ⌝
    | WaitingForReaders, RLocked num_readers =>
        "%Hblocked" ∷
        ⌜ Z.of_nat outstanding_reader_wait + Z.of_nat num_readers + uint.Z reader_sem ≤ sint.Z reader_wait ∧
          (writer_sem = W32 0 ∨ writer_sem = W32 1 ∧ reader_wait = W32 0) ⌝
    | IsLocked, Locked =>
        "%Hlocked" ∷
        ⌜ writer_sem = W32 0 ∧ reader_wait = W32 0 ∧ reader_sem = W32 0 ⌝
    | _, _ => False
    end.

Local Ltac rwauto :=
  solve [repeat first [eexists || done || subst || word || split || f_equal || intuition ||
                               simplify_eq || destruct decide || unfold sync.rwmutexMaxReaders in *]].

Lemma step_rlock_fast γ writer_sem reader_sem reader_count reader_wait state :
  0 ≤ (sint.Z (word.add reader_count (W32 1))) →
  own_toks γ.(rlock_overflow_gn) 1 -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  ∃ num_readers,
    ⌜ state = RLocked num_readers ⌝ ∧
    own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait (RLocked (num_readers + 1)).
Proof.
  iIntros "%Hpos Hrlock Hinv". iNamed "Hinv".
  iCombine "Hrlock Hrlocks" as "Hrlocks".
  iCombine "Hrlock_overflow Hrlocks" gives %Hoverflow.
  destruct wl; first last.
  1-3: rwauto.
  { destruct state; first last. { iNamed "Hinv". done. }
    iNamed "Hinv". intuition. subst. iExists _; iSplitR; first done.
    iFrame. iExists (word.add pos_reader_count (W32 1)).
    iSplitL "Hrlocks". { iApply to_named. iExactEq "Hrlocks". rwauto. }
    iPureIntro. rwauto. }
Qed.

Lemma step_rlock_fail_slow γ writer_sem reader_sem reader_count reader_wait state :
  (sint.Z (word.add reader_count (W32 1))) < 0 →
  own_toks γ.(rlock_overflow_gn) 1 -∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1)) reader_wait state.
Proof.
  iIntros "%Hpos Hrlock Hinv". iNamed "Hinv".
  iCombine "Hrlock Hrlocks" as "Hrlocks".
  iCombine "Hrlock_overflow Hrlocks" gives %Hoverflow.
  destruct state, wl.
  all: iNamed "Hinv"; try done; try (iExists _; iSplitR; first done).
  all: iFrame; iExists (word.add pos_reader_count (W32 1));
    iSplitL "Hrlocks"; [iApply to_named; iExactEq "Hrlocks"; rwauto| ].
  all: iPureIntro; rwauto.
Qed.

Lemma step_rlock_slow γ writer_sem reader_sem reader_count reader_wait state :
  0 < uint.Z reader_sem →
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state -∗
  ∃ num_readers,
    ⌜ state = RLocked num_readers ⌝ ∧
    own_RWMutex_invariant γ writer_sem (word.sub reader_sem (W32 1)) reader_count reader_wait (RLocked (S num_readers)).
Proof.
  iIntros "%Hsem_acq Hinv".
  iNamed "Hinv". destruct state.
  - destruct wl; iNamed "Hinv"; try (iExists _; iSplitR; first done).
    all: intuition; subst; iFrame; iPureIntro; rwauto.
  - iNamed "Hinv"; destruct wl; iNamed "Hinv"; rwauto.
Qed.

Lemma step_runlock_fast γ writer_sem reader_sem reader_count reader_wait num_readers :
  0 ≤ sint.Z (word.sub reader_count (W32 1)) →
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait (RLocked (S num_readers)) -∗
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.sub reader_count (W32 1)) reader_wait (RLocked num_readers).
Proof.
  iIntros "%Hfast Hinv". iNamed "Hinv".
  iCombine "Hrlock_overflow Hrlocks" gives %Hoverflow.
  iDestruct (own_toks_plus _ _ 1 with "Hrlocks") as "[Hr Hrlocks]".
  destruct wl; iNamed "Hinv"; try done.
  - iFrame. iExists (word.sub pos_reader_count (W32 1)).
    iSplitL "Hrlocks". { iApply to_named. iExactEq "Hrlocks". rwauto. }
    iPureIntro. rwauto.
  - rwauto. - rwauto.
Qed.

Lemma step_runlock_slow_start writer_sem reader_sem reader_count reader_wait wl state :
  0 ≤ sint.Z (word.sub reader_count (W32 1)) →
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait (RLocked (S num_readers)) -∗
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.sub reader_count (W32 1)) reader_wait (RLocked num_readers).
Proof.
  intros Hinv.
  unfold pure_RWMutex_invariant, reader_count_abs in *.
  destruct decide.
  { destruct Hinv as (? & ? & ?).
Qed.

Lemma step_runlock_slow_finish writer_sem reader_sem reader_count reader_wait wl state :
  0 ≤ sint.Z (word.sub reader_count (W32 1)) →
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait (RLocked (S num_readers)) -∗
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem (word.sub reader_count (W32 1)) reader_wait (RLocked num_readers).
Proof.
  intros Hinv.
  unfold pure_RWMutex_invariant, reader_count_abs in *.
  destruct decide.
  { destruct Hinv as (? & ? & ?).
Qed.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_pkg_init sync }}}
    sync @ "NewCond" #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_auto.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  iNamed "Hl".
  iPersist "HL".
  iFrame "#". done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef Hc]".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @ sync @ "Cond'ptr" @ "Wait" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(#Hcond & #Hlock & HR)".
  iNamed "Hcond".
  wp_method_call. wp_call.
  iNamed "Hlock".
  wp_auto.
  wp_apply ("H_Unlock" with "[$]").
  wp_apply ("H_Lock" with "[$]") as "?".
  iApply "HΦ". done.
Qed.

Definition is_sema (x : loc) γ N : iProp Σ :=
  inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).

Definition own_sema γ (v : w32) : iProp Σ :=
  ghost_var γ (1/2) v.

Lemma wp_runtime_Semacquire (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semacquire" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_for.
  wp_bind (! _)%E.
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  unshelve iApply (wp_typed_Load with "[$Hs]"); try tc_solve.
  { done. }
  iNext.
  iIntros "Hs".
  iMod ("Hclose" with "[$]") as "_".
  iModIntro.
  wp_auto.
  destruct bool_decide eqn:Hnz.
  { (* keep looping *)
    wp_auto.
    wp_for_post.
    iFrame.
  }

  (* try to acquire *)
  rewrite bool_decide_eq_false in Hnz.
  wp_auto.
  wp_bind (CmpXchg _ _ _).
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  destruct (decide (v = v0)).
  {
    subst. iMod "HΦ" as (?) "[Hv2 HΦ]".
    iCombine "Hv Hv2" as "Hv" gives %[_ <-].
    iMod (ghost_var_update with "Hv") as "[Hv Hv2]".
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iNext. iIntros "Hs".
    iMod ("HΦ" with "[] [$]") as "HΦ".
    { iPureIntro.
      (* FIXME: word *)
      assert (uint.nat v0 ≠ O).
      { intros ?. apply Hnz. word. }
      word.
    }
    iModIntro.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    done.
  }
  { (* cmpxchg will fail *)
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve.
    { done. }
    { naive_solver. }
    iNext. iIntros "Hs".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

Lemma wp_runtime_SemacquireWaitGroup (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_SemacquireWaitGroup" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_apply (wp_runtime_Semacquire with "[$]").
  iFrame.
Qed.

Lemma wp_runtime_Semrelease (sema : loc) γ N (_u1 : bool) (_u2 : w64):
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (own_sema γ (word.add v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semrelease" #sema #_u1 #_u2 {{ Φ }}.
Proof.
Admitted.

Local Definition enc (low high : w32) : w64 :=
  word.add (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

Local Ltac local_word :=
  try apply word.unsigned_inj;
  repeat try (
      rewrite !word.unsigned_sru // ||
      rewrite word.unsigned_add ||
      rewrite word.unsigned_slu // ||
      rewrite !Z.shiftr_div_pow2 // ||
      rewrite Z.shiftl_mul_pow2 //
    );
  word
.

Local Lemma enc_get_high (low high : w32) :
  W32 (uint.Z (word.sru (enc low high) (W64 32))) = high.
Proof.
  local_word.
Qed.

Local Lemma enc_get_low (low high : w32) :
  W32 (uint.Z (enc low high)) = low.
Proof.
  local_word.
Qed.

Local Lemma enc_add_high (low high delta : w32) :
  word.add (enc low high) (word.slu (W64 (uint.Z delta)) (W64 32)) =
  enc low (word.add high delta).
Proof.
  local_word.
Qed.

Local Lemma enc_add_low (low high delta : w32) :
  uint.Z (word.add low delta) = uint.Z low + uint.Z delta →
  word.add (enc low high) (W64 (uint.Z delta)) =
  enc (word.add low delta) high.
Proof.
  intros. local_word.
Qed.

Local Lemma enc_inj (low high low' high' : w32) :
  enc low high = enc low' high' →
  low = low' ∧ high = high'.
Proof.
  intros Heq.
  split.
  - erewrite <-(enc_get_low low high).
    rewrite Heq enc_get_low //.
  - erewrite <-(enc_get_high low high).
    rewrite Heq enc_get_high //.
Qed.

Local Lemma enc_0 :
  W64 0 = enc (W32 0) (W32 0).
Proof. reflexivity. Qed.

Record WaitGroup_names := {
    counter_gn : gname ;
    sema_gn : gname ;
    waiter_gn : gname ;
    zerostate_gn : gname ;
  }.

Implicit Type γ : WaitGroup_names.

(* FIXME: opaque *)
Definition own_WaitGroup_waiters γ (possible_waiters : w32) : iProp Σ :=
  own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (uint.nat possible_waiters).

(* FIXME: opaque *)
Definition own_WaitGroup_wait_token γ : iProp Σ :=
  own_toks γ.(waiter_gn) 1.

Local Definition is_WaitGroup_inv wg γ N : iProp Σ :=
  inv (N.@"wg") (∃ (counter waiters sema possible_waiters : w32) unfinished_waiters,
  "Hsema" ∷ own_sema γ.(sema_gn) sema ∗
  "Hsema_zerotoks" ∷  own_toks γ.(zerostate_gn) (uint.nat sema) ∗

  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ waiters ≠ W32 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  (* When Add's caller has [own_waiters 0], this resource implies that there are no waiters. *)
  "Hwait_toks" ∷  own_toks γ.(waiter_gn) (uint.nat waiters) ∗
  "Hunfinished_wait_toks" ∷ own_toks γ.(waiter_gn) unfinished_waiters ∗

  "Hzeroauth" ∷ own_tok_auth γ.(zerostate_gn) unfinished_waiters ∗

  (* keeping this to maintain that the number of waiters does not overflow. *)
  "Hwaiters_bounded" ∷ own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (uint.nat possible_waiters) ∗

  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ O → waiters = W32 0 ∧ counter = W32 0 ⌝ ∗
  "%Hunfinished_bound" ∷ ⌜ Z.of_nat unfinished_waiters < 2^32 ⌝
  )%I.

(* FIXME: opaque *)
Definition is_WaitGroup wg γ N : iProp Σ :=
  "#Hsem" ∷ is_sema (struct.field_ref_f sync.WaitGroup "sema" wg) γ.(sema_gn) (N.@"sema") ∗
  "#Hinv" ∷ is_WaitGroup_inv wg γ N.

#[local]
Instance if_sumbool_timeless {PROP : bi} (P Q : PROP) {_:Timeless P} {_:Timeless Q} A B
  (x : sumbool A B) :
  Timeless (if x then P else Q).
Proof. apply _. Qed.

(* Prepare to Wait() *)
Lemma alloc_wait_token wg γ N (w : w32) :
  uint.Z (word.add w (W32 1)) = uint.Z w + 1 →
  is_WaitGroup wg γ N -∗
  own_WaitGroup_waiters γ w ={↑N}=∗ own_WaitGroup_waiters γ (word.add w (W32 1)) ∗ own_WaitGroup_wait_token γ.
Proof.
  intros. iIntros "[_ #Hinv] H".
  iInv "Hinv" as ">Hi". iNamed "Hi".
  iCombine "Hwaiters_bounded H" gives %[_ ->].
  iCombine "Hwaiters_bounded H" as "H". rewrite dfrac_op_own Qp.half_half.
  iMod (own_tok_auth_plus 1 with "H") as "[H Htok]".
  iModIntro. rewrite <- (Z2Nat.inj_add _ 1) by word. rewrite -H.
  iDestruct "H" as "[H1 H2]". iSplitR "Htok H2"; by iFrame.
Qed.

Lemma waiters_none_token_false γ :
  own_WaitGroup_waiters γ (W32 0) -∗ own_WaitGroup_wait_token γ -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %H. word.
Qed.

(* FIXME: Opaque *)
Definition own_WaitGroup γ (counter : w32) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.

Lemma start_WaitGroup N wg_ptr :
  wg_ptr ↦ (default_val sync.WaitGroup.t) ={⊤}=∗
  ∃ γ,
  is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ (W32 0) ∗ own_WaitGroup_waiters γ (W32 0).
Proof.
  iIntros "H".
  iDestruct (struct_fields_split with "H") as "H".
  iNamed "H". simpl.

  iMod (ghost_var_alloc (W32 0)) as "[%counter_gn [Hctr1 Hctr2]]".
  iMod (ghost_var_alloc (W32 0)) as "[%sema_gn [Hs1 Hs2]]".
  iMod (own_tok_auth_alloc) as "[%waiter_gn [Hwaiters Hw2]]".
  iMod (own_tok_auth_alloc) as "[%zerostate_gn Hzerostate]".

  iExists {| sema_gn := sema_gn; counter_gn := counter_gn; zerostate_gn := zerostate_gn; waiter_gn := waiter_gn |}.
  iFrame "∗#".
  unfold is_WaitGroup.
  iMod (inv_alloc with "[Hsema Hs2]") as "$".
  { iFrame. }
  iDestruct "Hstate" as "[Hstate Hstate2]".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 zerostate_gn) as "?".
  iMod (inv_alloc with "[-]") as "$".
  { iNext. repeat iExists (W32 0). iFrame. done. }
  done.
Qed.

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (uint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (uint.Z delta')) (W64 32).
Proof.
  intros ->. local_word.
Qed.

Lemma atomic_Uint64_inj a b c a' b' c' :
  atomic.Uint64.mk a b c = atomic.Uint64.mk a' b' c' →
  c = c'.
Proof.
  inversion 1.
  done.
Qed.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ N :
  let delta' := (W32 (uint.Z delta)) in
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) -∗
               own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Add" #delta {{ Φ }}.
Proof.
  intros delta'.
  wp_start as "#His".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto.
  wp_apply wp_Uint64__Add.
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iNamed "His".
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iCombine "Hctr_wg Hwg" as "Hctr" gives %[_ ->].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    iDestruct "HnoWaiters" as "[%|HnoWaiter]"; first by exfalso.
    iCombine "HnoWaiter Hwait_toks_wg" gives %Hbad.
    exfalso. apply Hw. word.
  }
  iCombine "Hptsto_wg Hptsto2_wg" as "Hptsto".
  iExists _. iFrame.
  rewrite (wg_delta_to_w32 delta') // enc_add_high.
  iMod (ghost_var_update (word.add oldc delta') with "Hctr") as "[Hctr_wg Hwg]".
  iIntros "[Hptsto1_wg Hptsto2_wg]".
  destruct unfinished_waiters.
  2:{
    iExFalso. destruct (Hunfinished_zero_wg ltac:(done)) as [-> ->].
    iDestruct "HnoWaiters" as "[%|HnoWaiters]"; first done.
    iCombine "HnoWaiters Hunfinished_wait_toks_wg" gives %Hbad. word.
  }
  subst.
  destruct (decide (word.add oldc delta' = W32 0 ∧ waiters ≠ W32 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    {
      iNamed "Hi". iNext. iFrame.
      rewrite decide_False; last intuition.
      iFrame. done.
    }
    iMod ("HΦ" with "[$] [$]").
    iModIntro.
    wp_auto.
    rewrite enc_get_high enc_get_low.

    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      (* FIXME: word should do these. *)
      rewrite word.signed_add in Hbad.
      replace (sint.Z (W32 0)) with 0 in * by reflexivity.
      rewrite word.swrap_inrange in Hbad; lia.
    }
    wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_auto.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_auto.
        destruct bool_decide eqn:Heq1.
        + wp_auto.
          replace (W32 (uint.Z delta)) with delta' by reflexivity.
          rewrite bool_decide_eq_true in Heq1.
          destruct bool_decide eqn:Heq2.
          * exfalso. rewrite bool_decide_eq_true in Heq2.
            { (* FIXME: word. *)
              assert (sint.Z oldc = 0).
              {
                word_cleanup.
                rewrite word.signed_add /word.swrap in Heq2_signed.
                word.
              }
              apply Heq0. intuition. exfalso. apply H2.
              { apply word.signed_inj. rewrite H //. }
              word.
            }
          * wp_auto. iFrame. done.
        + wp_auto. iFrame. done.
    }
    iIntros (?) "[% H]". iNamed "H".
    subst.
    wp_auto.
    destruct (bool_decide) eqn:Heq1.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    rewrite bool_decide_eq_false in Heq1.
    wp_auto.
    rewrite bool_decide_true.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    apply not_and_l in HnoWake, HnotInWakingState.
    destruct HnoWake as [|].
    2:{ by apply dec_stable. }
    destruct HnotInWakingState as [|].
    2:{ by apply dec_stable. }
    apply Znot_gt_le in Heq1.
    exfalso.
    (* FIXME: word *)
    apply H. clear H. apply word.signed_inj.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    intuition.
    apply Z.le_antisymm.
    { word. }
    { word_cleanup.
      rewrite word.signed_add /word.swrap in H2 |- *.
      word. }
  }

  (* will have to wake *)
  iRename "Hptsto2_wg" into "Hptsto". (* not going back to invariant. *)
  iMod "Hmask" as "_".
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_".
  {
    iNamed "Hi". iNext.
    iFrame. rewrite decide_True; last intuition. done.
  }
  iMod ("HΦ" with "[$] [$]") as "HΦ".
  iModIntro.
  wp_auto. rewrite enc_get_high enc_get_low.

  destruct bool_decide eqn:Hbad.
  {
    exfalso.
    rewrite bool_decide_eq_true in Hbad.
    (* FIXME: word should do these. *)
    rewrite word.signed_add in Hbad.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    rewrite word.swrap_inrange in Hbad; lia.
  }
  wp_auto.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_auto.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_auto.
      destruct bool_decide eqn:Heq1.
      + wp_auto.
        replace (W32 (uint.Z delta)) with delta' by reflexivity.
        rewrite bool_decide_eq_true in Heq1.
        destruct bool_decide eqn:Heq2.
        * exfalso. rewrite bool_decide_eq_true in Heq2.
          { (* FIXME: word. *)
            assert (sint.Z oldc = 0).
            {
              word_cleanup.
              rewrite word.signed_add /word.swrap in Heq2_signed.
              word.
            }
            apply Heq0. intuition. exfalso. apply H4.
            { apply word.signed_inj. rewrite H //. }
            word.
          }
        * wp_auto. iFrame. done.
      + wp_auto. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. word. }
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. }
  wp_auto.
  wp_apply wp_Uint64__Load.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".
  iModIntro.
  wp_auto.
  rewrite bool_decide_true //.

  (* want to get a bunch of unfinisheds. *)
  wp_auto.
  wp_apply wp_Uint64__Store.
  iInv "Hinv" as ">Hi" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  clear Hunfinished_zero_wg sema.
  iNamedSuffix "Hi" "_wg".
  iClear "Hptsto2_wg".
  iCombine "Hptsto Hptsto_wg"  gives %[_ Heq].
  apply atomic_Uint64_inj in Heq.
  apply enc_inj in Heq as [<- <-].
  iCombine "Hptsto Hptsto_wg" as "Hptsto".
  iExists _. iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".
  destruct (unfinished_waiters) eqn:Huf.
  2:{ exfalso. specialize (Hunfinished_zero_wg ltac:(word)). intuition. }
  clear Hunfinished_zero_wg.
  iClear "Hunfinished_wait_toks_wg".
  iCombine "Hzeroauth_wg Hsema_zerotoks_wg" gives %Hs.
  replace (sema) with (W32 0) by word.
  clear Huf Hs unfinished_waiters sema.
  iMod (own_tok_auth_plus (uint.nat waiters) with "[$Hzeroauth_wg]") as "[Hzeroauth_wg Hzerotoks_wg]".
  iEval (rewrite enc_0) in "Hptsto".
  iDestruct "Hptsto" as "[Hptsto1_wg Hptsto2_wg]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod (own_toks_0 γ.(waiter_gn)) as "Hwait_toks'_wg".
  iRename "Hzerotoks_wg" into "Hzerotoks". (* remove from invariant. *)
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_".
  { iNext. iNamed "Hi". iFrame "Hptsto1_wg ∗". iPureIntro. split; [done | word]. }
  iModIntro.
  wp_auto.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : w32),
        "w" ∷ w_ptr ↦ wrem ∗
        "Hzerotoks" ∷ own_toks γ.(zerostate_gn) (uint.nat wrem)
    )%I with "[$]" as "HloopInv".

  wp_for.
  iNamed "HloopInv".
  wp_auto.
  destruct bool_decide eqn:Hwrem.
  { (* no more waiters to wake up. *)
    rewrite decide_False; last naive_solver.
    rewrite decide_True //.
    wp_auto. iFrame.
  }

  (* wake up another waiter *)
  rewrite bool_decide_eq_false in Hwrem.
  rewrite decide_True //.
  wp_auto.
  wp_apply (wp_runtime_Semrelease with "[$]").
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame "Hsema_wg".
  iIntros "Hsema_wg".
  iMod "Hmask" as "_".
  replace (uint.nat wrem)%nat with (1+(uint.nat (word.sub wrem (W32 1))))%nat.
  2:{ (* FIXME: word *) apply w32_val_neq in Hwrem. word. }
  iDestruct (own_toks_plus with "Hzerotoks") as "[Hzerotok Hzerotoks]".
  iCombine "Hsema_zerotoks_wg Hzerotok" as "Hsema_zerotok_wg".
  iCombine "Hzeroauth_wg Hsema_zerotok_wg" gives %Hbound.
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]").
  {
    iNamed "Hi". iFrame.
    replace (uint.nat (word.add sema (W32 1))) with ((uint.nat sema) + 1)%nat by word.
    iFrame. done.
  }
  iModIntro. wp_auto. wp_for_post. iFrame.
Qed.

Lemma wp_WaitGroup__Done (wg : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc - 1 < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) -∗
               own_WaitGroup γ (word.sub oldc (W32 1)) ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Done" #() {{ Φ }}.
Proof.
  wp_start as "#His".
  wp_auto.
  wp_apply (wp_WaitGroup__Add with "[$]").
  iMod "HΦ". iNamed "HΦ".
  replace (W32 (uint.Z (W64 (-1)))) with (W32 (-1)) by done.
  replace (sint.Z (W32 (-1))) with (-1) by done.
  iModIntro. iFrame "Hwg HnoWaiters". iSplitR.
  { word. }
  iIntros "Hw Hctr".
  iMod ("HΦ" with "[$] [Hctr]") as "HΦ".
  { iExactEq "Hctr". repeat f_equal. word. }
  iModIntro. wp_auto. iApply "HΦ".
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) (delta : w64) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N ∗ own_WaitGroup_wait_token γ -∗
  (|={⊤∖↑N, ∅}=>
     ∃ oldc,
       own_WaitGroup γ oldc ∗ (⌜ sint.Z oldc = 0 ⌝ → own_WaitGroup γ oldc ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token γ -∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Wait" #() {{ Φ }}.
Proof.
  wp_start as "(#Hwg & HR_in)". iNamed "Hwg".
  wp_auto.
  wp_for_core. (* TODO: need to set later credits *)
  wp_auto.
  rewrite decide_True //. wp_auto.
  wp_apply (wp_Uint64__Load).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  destruct (decide (counter = W32 0)).
  { (* counter is zero, so can return. *)
    subst.

    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iModIntro.
    iCombine "Hwg Hctr_wg" gives %[_ ->].
    iExists _.
    iFrame.
    iIntros "Hptsto_wg".
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    { iNamed "Hi". by iFrame. }
    iModIntro.
    wp_auto. rewrite enc_get_high enc_get_low bool_decide_true //=.
    wp_auto.
    wp_for_post.
    by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto_wg".
  iMod "Hmask" as "_".

  iCombine "HR_in Hwait_toks_wg" as "Hwait_toks'_wg".
  iCombine "Hwaiters_bounded_wg Hwait_toks'_wg" gives %HwaitersLe.
  iDestruct (own_toks_plus with "Hwait_toks'_wg") as "[HR_in Hwait_toks_wg]".
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]").
  { iNamed "Hi". by iFrame. }
  iModIntro.
  wp_auto.
  rewrite enc_get_high enc_get_low bool_decide_false //.
  wp_auto.
  replace (1%Z) with (uint.Z (W32 1)) by reflexivity.
  rewrite -> enc_add_low by word.
  wp_apply (wp_Uint64__CompareAndSwap).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  setoid_rewrite bool_decide_decide.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists (enc waiters0 counter0).
  destruct (decide (_ = _)) as [Heq|Hneq].
  {
    apply enc_inj in Heq as [-> ->].
    rewrite decide_False.
    2:{ naive_solver. }
    iCombine "Hptsto_wg Hptsto2_wg" as "$".
    iSplitR; first done.
    iIntros "[Hptsto_wg Hptsto2_wg]".
    iCombine "HR_in Hwait_toks_wg" as "Hwait_toks_wg".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    {
      iNext. iNamed "Hi". repeat iExists _. iFrame "Hptsto_wg ∗".
      replace (uint.nat (word.add waiters (W32 1))) with (1 + uint.nat waiters)%nat by word.
      simpl. iFrame.
      iSplitL.
      { by destruct decide. }
      iPureIntro. split; last done.
      intros Hun. exfalso. naive_solver.
    }
    iModIntro.
    wp_auto.
    clear sema n unfinished_waiters Hunfinished_zero_wg Hunfinished_bound_wg
               unfinished_waiters0 Hunfinished_zero_wg0 Hunfinished_bound_wg0.

    wp_apply (wp_runtime_SemacquireWaitGroup with "[$]").
    iInv "Hinv" as ">Hi" "Hclose".
    iNamedSuffix "Hi" "_wg".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame "Hsema_wg".
    iIntros "%Hsem Hsema_wg".
    destruct (uint.nat sema) eqn:Hsema.
    { exfalso. lia. }
    replace (S n) with (1 + n)%nat by done.
    iDestruct (own_toks_plus with "Hsema_zerotoks_wg") as "[Hzerotok Hsema_zerotoks_wg]".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    {
      iNext. iNamed "Hi". iFrame.
      replace (uint.nat (word.sub sema (W32 1))) with n by word.
      iFrame. done.
    }
    iModIntro.
    wp_auto.
    wp_apply (wp_Uint64__Load).
    iInv "Hinv" as ">Hi" "Hclose".
    iClear "v w state". clear v_ptr counter w_ptr waiters state_ptr HwaitersLe.
    clear unfinished_waiters sema n Hsema Hsem Hunfinished_zero_wg Hunfinished_bound_wg.
    iNamedSuffix "Hi" "_wg".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _. iFrame "Hptsto_wg".
    iCombine "Hzeroauth_wg Hzerotok" gives %Hunfinished_pos.
    specialize (Hunfinished_zero_wg ltac:(lia)) as [-> ->].
    iIntros "Hptsto_wg".
    iMod "Hmask" as "_".

    (* now, deallocate Htok. *)
    destruct unfinished_waiters; first by (exfalso; lia).
    iMod (own_tok_auth_delete_S with "Hzeroauth_wg Hzerotok") as "Hzeroauth_wg".
    replace (S _) with (1 + unfinished_waiters)%nat by done.
    iDestruct (own_toks_plus with "Hunfinished_wait_toks_wg") as "[HR Hunfinished_wait_toks_wg]".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iCombine "Hwg Hctr_wg" gives %[_ ->].
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    { iNamed "Hi". iFrame. iPureIntro. split; [done | word]. }
    iModIntro.
    wp_auto.
    wp_for_post.
    iApply "HΦ". done.
  }
  {
    iFrame "Hptsto_wg".
    iSplitR; first done.
    iIntros "Hptsto_wg".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    { iNamed "Hi". iFrame. done. }
    iModIntro. wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
