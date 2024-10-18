From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From New.code Require Export sync.
From New.proof Require Import proof_prelude.
From Perennial.algebra Require Import map.

Set Default Proof Using "Type".

Class syncG Σ := {
    #[global] wg_tokG :: mapG Σ u64 unit;
    #[global] wg_totalG :: ghost_varG Σ u64
  }.

Definition syncΣ := #[mapΣ u64 unit ; ghost_varΣ u64].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Module Mutex.
Record t := mk {
    state : bool
}.
End Mutex.

Instance into_val_Mutex `{ffi_syntax} : IntoVal Mutex.t :=
  {|
    to_val_def := λ v, struct.val Mutex [("state" ::= #v.(Mutex.state))]%V
  |}.

Program Instance into_val_typed_Mutex `{ffi_syntax} : IntoValTyped Mutex.t Mutex :=
{| default_val := Mutex.mk false |}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.
Next Obligation.
  (* FIXME: [solve_zero_val] tactic *)
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_unseal /=.
  rewrite zero_val_eq /= !to_val_unseal //.
Qed.
Next Obligation.
  (* FIXME: automation for this *)
  rewrite to_val_unseal => ? x y Heq.
  rewrite /= struct.val_unseal /= in Heq.
  inversion Heq.
  destruct x, y.
  f_equal.
  simpl in *.
  apply to_val_inj in H0. subst. done.
Qed.
Final Obligation. solve_decision. Qed.

Program Instance into_val_struct_Mutex_state `{ffi_syntax} :
  IntoValStructField "state" [("state" :: boolT)%struct] Mutex.t bool Mutex.state.
Final Obligation.
intros. by rewrite to_val_unseal /= struct.val_unseal /= to_val_unseal /=.
Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  inv nroot (
        ∃ b : bool,
          (m ↦s[ Mutex :: "state" ]{# 1/4} b) ∗
                  if b then True else
                    m ↦s[Mutex :: "state"]{# 3/4} b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[Mutex :: "state"]{# 3/4} true.

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

Theorem init_Mutex R E m : m ↦# (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "Hl HR".
  simpl.
  (* FIXME: typeclass for relating record projections to struct fields. *)
  iDestruct (struct_fields_split with "Hl") as "Hl".
  { done. }
  { apply _. }
  iDestruct "Hl" as "[Hl _]".
  unshelve iSpecialize ("Hl" $! _ _ _ _ _ _ _); try tc_solve.
  simpl. iNamed "Hl".
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
  wp_call.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_pures.
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
    rewrite /locked. wp_pures.
    iApply "HΦ".
    eauto with iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock' m :
  {{{ True }}}
    Mutex__Unlock #m
  {{{ (f : func.t), RET #f;
      ∀ R,
    {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} #f #() {{{ RET #(); True }}}
  }}}.
Proof.
  iIntros (Ψ) "_ HΨ".
  wp_call.
  iApply "HΨ". iIntros (R).
  iIntros (Φ) "!# (#Hinv & Hlocked & HR) HΦ".
  wp_pures.
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
  iSplitR "HΦ"; last by wp_pures; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

Lemma wp_Mutex__Unlock m R :
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} Mutex__Unlock #m #() {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hinv & Hlocked & HR) HΦ".
  wp_bind (Mutex__Unlock _).
  wp_apply wp_Mutex__Unlock'. iIntros (?) "Hspec".
  wp_apply ("Hspec" with "[$Hinv $Hlocked $HR]").
  by iApply "HΦ".
Qed.

Definition is_Locker (i : interface.t) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} (interface.get "Lock" #i) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} (interface.get "Unlock" #i) #() {{{ RET #(); True }}})
.

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_Mutex m R -∗
  is_Locker (interface.mk #m Mutex__mset_ptr) (own_Mutex m ∗ R).
Proof.
  iIntros "#?".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_pures.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_pures.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  c ↦#□ m.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ True }}}
    NewCond #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  wp_call. wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_pures.
  iApply "HΦ". iMod (typed_pointsto_persist with "Hc") as "$".
  done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    Cond__Signal #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    Cond__Broadcast #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    Cond__Wait #c #()
  {{{ RET #(); R }}}.
Proof.
  iIntros (Φ) "(#Hcond&#Hlock&HR) HΦ".
  unfold Cond__Wait.
  wp_pures.
  iNamed "Hlock". iNamed "Hcond".
  wp_load.
  wp_apply ("H_Unlock" with "[$]").
  wp_pures.
  wp_load.
  wp_apply ("H_Lock" with "[$]").
  iIntros "HR".
  wp_pures.
  iApply "HΦ". done.
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
        "Hv" ∷ vptr ↦# (W64 $ size remaining) ∗
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
    mu ↦# (default_val Mutex.t) ∗
    vptr ↦# (W64 0)
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
  iExists ∅, (U64 0%Z).
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
    WaitGroup__Add wg #(W64 1)
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
            is_Locker is_Cond
            is_WaitGroup own_WaitGroup own_WaitGroup_token own_free_WaitGroup.
