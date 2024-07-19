From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import persistent_readonly.
From New.code Require Export sync.
From New.proof Require Import proof_prelude.
From Perennial.algebra Require Import map.

Set Default Proof Using "Type".

Class syncG Σ := {
    wg_tokG :> mapG Σ u64 unit;
    wg_totalG :> ghost_varG Σ u64
  }.

Definition syncΣ := #[mapΣ u64 unit ; ghost_varΣ u64].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  inv nroot (
        ∃ b : bool,
          (m ↦s[ Mutex :: "state" ]{# 1/4} #b) ∗
                  if b then True else
                    m ↦s[Mutex :: "state"]{# 3/4} #b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[Mutex :: "state"]{# 3/4} #true.

Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" as "H".
  (* FIXME: need
  iDestruct (struct_field_pointsto_frac_valid with "H") as %Hval. *)
  admit.
Admitted.

Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_Mutex m).
Proof. apply _. Qed.

Theorem init_Mutex R E m : m ↦[Mutex] (zero_val $ Mutex) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "Hl HR".
  simpl.
  iDestruct (struct_fields_split with "Hl") as "Hl".
  { done. }
  { apply _. }
  iEval (repeat rewrite ?zero_val_eq ?struct.val_unseal ?lookup_empty /=) in "Hl".
  iNamed "Hl".
  iMod (inv_alloc nroot _ (_) with "[Hstate HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hstate".
    iDestruct "Hstate" as "[$$]".
  }
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    Mutex__Lock #m #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_apply (wp_typed_cmpxchg_fail with "[$]").
    { repeat econstructor. }
    { repeat econstructor. }
    { naive_solver. }
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_pures.
    by iApply "IH".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_apply (wp_typed_cmpxchg_suc with "[$]").
    { econstructor. }
    { econstructor. }
    { done. }
    iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_pures.
    iApply "HΦ".
    eauto with iFrame.
Qed.

Lemma wp_Mutex__Unlock m R :
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} Mutex__Unlock #m #() {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hinv & Hlocked & HR) HΦ".
  wp_rec.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as (b) "[>Hl _]".

  unfold own_Mutex.
  iCombine "Hl Hlocked" gives %[_ [=]]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  wp_apply (wp_typed_cmpxchg_suc with "[$]").
  { econstructor. }
  { econstructor. }
  { done. }
  iIntros "Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_pures; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

(** This means [c] is a condvar with underyling Mutex at address [m]. *)
Definition is_Cond (c : loc) (m : loc) : iProp Σ :=
  readonly (c ↦ #m).

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : loc) :
  {{{ True }}}
    NewCond #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_rec. wp_pures. wp_apply wp_fupd.
  wp_apply wp_alloc_untyped; [ auto | ].
  iIntros (c) "Hc".
  iMod (readonly_alloc_1 with "Hc") as "Hcond".
  wp_pures.
  iApply "HΦ". by iFrame.
Qed.

Theorem wp_Cond__Signal c m :
  {{{ is_Cond c m }}}
    Cond__Signal #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_rec. wp_pures.
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    Cond__Broadcast #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_rec. wp_pures.
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Mutex m R ∗ own_Mutex m ∗ R }}}
    Cond__Wait #c #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof using syncG0. (* XXX: not sure which part of the proof uses syncG, but also don't care. *)
  iIntros (Φ) "(#Hcond&#Hlock&Hlocked&HR) HΦ".
  unfold Cond__Wait.
  wp_pures.

  iMod (readonly_load with "Hcond") as (q) "Hc".
  wp_untyped_load.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $HR]").
  wp_pures.
  wp_untyped_load.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "(Hlocked&HR)".
  wp_pures.
  iApply "HΦ". iModIntro.
  iFrame.
Qed.

Record waitgroup_names :=
  mkwaitgroup_names {
    tok_gn:gname;
    total_gn:gname
  }.

Implicit Types (γ : waitgroup_names).

(** Represents permission to call Done() once on a WaitGroup(). *)
Definition own_WaitGroup_token γ (i:u64) : iProp Σ := i ⤳[γ.(tok_gn)] ().

(** This means [wg] is a pointer to a WaitGroup which logically associates the
    proposition [P i] with the ith call to Add(). This means that in order to
    call Done(), one must logically decide which call to Add() is being
    cancelled out (i.e. which [i]) and must provide [P i] for that particular
    call. [γ] is used to name WaitGroup tokens, which encode the fact that the
    ith call to Add() can only be Done()'d once. *)
Definition is_WaitGroup wg γ P : iProp Σ :=
  ∃ (m vptr:loc),
    ⌜wg = (#m, #vptr)%V⌝ ∗
    is_Mutex m (
      ∃ (remaining:gset u64) (total:u64),
        "%Hremaining" ∷ ⌜(∀ r, r ∈ remaining → uint.nat r < uint.nat total)⌝ ∗
        "Htotal" ∷ ghost_var γ.(total_gn) (1/2) total ∗
        "Hv" ∷ vptr ↦[uint64T] #(size remaining) ∗
        "Htoks" ∷ ([∗ set] i ∈ (fin_to_set u64), ⌜i ∈ remaining⌝ ∨ own_WaitGroup_token γ i) ∗
        "HP" ∷ ([∗ set] i ∈ (fin_to_set u64), ⌜ uint.nat i ≥ uint.nat total⌝ ∨ ⌜i ∈ remaining⌝ ∨ (□ (P i)))
    ).

(** This denotes exclusive ownership of the permission to call Add() on the
    waitgroup, and the fact that Add() has been called [n] times. *)
Definition own_WaitGroup (wg:val) γ (n:u64) (P:u64 → iProp Σ) : iProp Σ :=
    ghost_var γ.(total_gn) (1/2) n ∗
    is_WaitGroup wg γ P.

(** This denotes exclusive ownership of a waitgroup which has never been
    Add()ed to and for which the logical predicate [P] is not yet decided. *)
Definition own_free_WaitGroup (wg:val) : iProp Σ :=
  ∃ (mu:loc) (vptr:loc),
    ⌜wg = (#mu, #vptr)%V⌝ ∗
    mu ↦[Mutex] (zero_val $ Mutex) ∗
    vptr ↦[uint64T] #0
.

Lemma own_WaitGroup_to_is_WaitGroup wg γ P n :
  own_WaitGroup wg γ n P -∗ is_WaitGroup wg γ P.
Proof. iIntros "[_ $]". Qed.

(* FIXME: zero_val for WaitGroup *)

Lemma free_WaitGroup_alloc P wg E :
  own_free_WaitGroup wg ={E}=∗ (∃ γ, own_WaitGroup wg γ 0 P ).
Proof.
  iIntros "Hwg".
  iDestruct "Hwg" as (??) "(%Hwg & His_Mutex & Hv)".
  iMod (ghost_map_alloc_fin ()) as (γtok) "Htokens".
  iMod (ghost_var_alloc (U64 0)) as (γtotal) "[Htotal Ht2]".
  iExists (mkwaitgroup_names γtok γtotal).
  iFrame.
  iExists _, _.
  iSplitL ""; first done.
  simpl.

  iMod (init_Mutex with "His_Mutex [-]") as "$"; last done.
  iNext.
  iExists ∅, (U64 0).
  rewrite size_empty.
  iFrame "Hv Htotal".
  iSplitL "".
  {
    iPureIntro.
    set_solver.
  }
  iSplitR "".
  {
    iApply (big_sepS_impl with "Htokens").
    iModIntro.
    iIntros.
    iRight.
    iFrame.
  }
  {
    iDestruct (big_sepS_emp with "[]") as "Htriv"; first done.
    iApply (big_sepS_impl with "Htriv").
    iModIntro.
    iIntros.
    iLeft.
    iPureIntro.
    word.
  }
Qed.

Lemma wp_WaitGroup__Add wg γ n P :
uint.nat (word.add n 1) > uint.nat n →
  {{{ own_WaitGroup wg γ n P }}}
    WaitGroup__Add wg #1
  {{{ RET #(); own_WaitGroup wg γ (word.add n 1) P ∗ own_WaitGroup_token γ n }}}.
Proof.
Admitted.

Lemma wp_WaitGroup__Done wg γ P n :
  {{{ is_WaitGroup wg γ P ∗ own_WaitGroup_token γ n ∗ □ P n }}}
    WaitGroup__Done wg
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_WaitGroup__Wait wg γ P n :
  {{{ own_WaitGroup wg γ n P }}}
    WaitGroup__Wait wg
  {{{ RET #(); [∗ set] i ∈ (fin_to_set u64), ⌜ uint.nat i ≥ uint.nat n ⌝ ∨ (P i) }}}.
Proof.
Admitted.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Cond
            is_WaitGroup own_WaitGroup own_WaitGroup_token own_free_WaitGroup.
