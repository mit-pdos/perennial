From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import persistent_readonly.
From Goose Require Export sync.
From Perennial.program_proof Require Import new_proof_prelude.
From Perennial.new_goose_lang Require Import exception typed_mem.
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
(* TODO: fix all the notation *)
Declare Custom Entry struct_field_type.
Notation "d ⋅ f" := (d, f) (in custom struct_field_type at level 80 ,
                                  d constr at level 49,
                                  f constr at level 49
                               ).
Notation "l ↦s[ df ] dq v" := (let '(d, f) := df in (struct.fieldRef_f d f l ↦[ struct.fieldTy d f ]{dq} v))%I
  (at level 50, dq custom dfrac at level 70,
                   df custom struct_field_type at level 80).

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  inv nroot (
        ∃ b : bool,
          (m ↦s[ Mutex ⋅ "state" ]{# 1/4} #b) ∗
                  if b then True else
                    m ↦s[Mutex ⋅ "state"]{# 3/4} #b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[Mutex ⋅ "state"]{# 3/4} #true.

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

(** Denotes ownership of a mutex for which the lock invariant is not yet
    decided *)
Definition own_uninit_Mutex (m: loc): iProp Σ := m ↦s[Mutex ⋅ "state"] #false.

Theorem init_Mutex R E m : own_uninit_Mutex m -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "Hl HR".
  iMod (inv_alloc nroot _ (_) with "[Hl HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    rewrite /own_uninit_Mutex.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    (* FIXME: *)
    iDestruct "Hl" as "[$$]".
  }
Qed.

(* FIXME: move this *)
Local Fixpoint struct_big_fields_rec l dq (d: descriptor) (fs:descriptor) (v:val): iProp Σ :=
  match fs with
  | [] => "_" ∷ ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => ("H" ++ f) ∷ l ↦s[d ⋅ f]{dq} v1 ∗
                    struct_big_fields_rec l dq d fs v2
    | _ => False
    end
  end.

Definition struct_fields l dq d v : iProp Σ := struct_big_fields_rec l dq d d v.

Theorem struct_fields_split l q d {dwf: struct.wf d} v :
  typed_pointsto l q (structT d) v ⊣⊢ struct_fields l q d v.
Proof.
Admitted.

Lemma wp_struct_fieldRef d f (l : loc) :
  {{{ True }}}
    struct.fieldRef d f #l
  {{{ RET #(struct.fieldRef_f d f l); True }}}
.
Proof.
  iIntros (?) "_ HΦ".
  Transparent struct.fieldRef. wp_lam. Opaque struct.fieldRef.
  wp_pures.
  unfold struct.fieldRef_f.
  rewrite Z.mul_1_r.
  by iApply "HΦ".
Qed.

Lemma wp_new_Mutex E:
  {{{ True }}}
    ref_to (structT Mutex) (zero_val (structT Mutex)) @ E
 {{{ m, RET #m; own_uninit_Mutex m }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply wp_ref_to.
  { apply zero_val_has_go_type. }
  iIntros (?) "Hl".
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl". simpl. iFrame.
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    Mutex__Lock #m
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  iLöb as "IH".
  wp_rec.
  wp_apply wp_struct_fieldRef.
  wp_bind (CmpXchg _ _ _).
  wp_pures.
  iInv nroot as ([]) "[Hl HR]".
  - wp_apply (wp_typed_cmpxchg_fail with "[$]").
    { done. }
    { repeat econstructor. } (* apply _. FIXME: tc search? *)
    { naive_solver. }
    { done. }
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_pures.
    by iApply "IH".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_cmpxchg_suc.
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_pures.
    iApply "HΦ".
    eauto with iFrame. *)
Admitted.

Lemma wp_Mutex__Unlock m R :
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} Mutex__Unlock #m {{{ RET #(); True }}}.
Proof.
  (*
  iIntros (? Φ) "(Hlock & Hlocked & HR) HΦ".
  iDestruct "Hlock" as (l ->) "#Hinv".
  rewrite /lock.release /=. wp_lam.
  wp_bind (CmpXchg _ _ _).
  iInv N as (b) "[>Hl _]".

  iDestruct (locked_loc with "Hlocked") as "Hl2".
  iDestruct (heap_pointsto_agree with "[$Hl $Hl2]") as %->.
  iCombine "Hl Hl2" as "Hl".
  rewrite Qp.quarter_three_quarter.
  wp_cmpxchg_suc.
  iModIntro.
  iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame. *)
Admitted.

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
  wp_call. wp_apply wp_fupd.
  wp_apply wp_alloc_untyped; [ auto | ].
  iIntros (c) "Hc".
  iMod (readonly_alloc_1 with "Hc") as "Hcond".
  wp_pures.
  iApply "HΦ". by iFrame.
Qed.

Theorem wp_Cond__Signal c m :
  {{{ is_Cond c m }}}
    Cond__Signal #c
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_call.
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    Cond__Broadcast #c
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_call.
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Mutex m R ∗ own_Mutex m ∗ R }}}
    Cond__Wait #c
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
    own_uninit_Mutex mu ∗
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
