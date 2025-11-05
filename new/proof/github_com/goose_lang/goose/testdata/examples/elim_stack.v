From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
From iris.algebra Require Import auth.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From New.golang.theory Require Import chan.
From iris.base_logic.lib Require Import saved_prop.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Class elimStackGhostStateG Σ := ElimStackGhostStateG {
  stack_listG :: ghost_varG Σ (list (go_string));
  push_parked_propG :: savedPropG Σ;
  pop_parked_predG :: savedPredG Σ (go_string * bool);
}.

Definition elimStackGhostStateΣ : gFunctors :=
  #[ ghost_varΣ (list (go_string));
     savedPropΣ; savedPredΣ (go_string * bool) ].

#[global] Instance subG_elimStackGhostStateG Σ :
  subG elimStackGhostStateΣ Σ → elimStackGhostStateG Σ.
Proof. solve_inG. Qed.

Section elim_stack.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ go_string}.
Context `{!elimStackGhostStateG Σ}.

Record stack_names := {
  stack_state_name : gname;
  exch_chan_name : chan_names;
  push_parked_prop_name : gname;
  pop_parked_pred_name : gname;
}.

(** Abstract stack representation *)
Definition stack_rep (γ: gname) (q: Qp) (l: list (go_string)) : iProp Σ :=
  ghost_var γ q l.

Notation stack_rep_full γ l := (stack_rep γ 1 l).
Notation stack_rep_half γ l := (stack_rep γ (1/2)%Qp l).

Lemma stack_rep_agree γ q1 q2 l1 l2 :
  stack_rep γ q1 l1 -∗ stack_rep γ q2 l2 -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2").
Qed.

Lemma stack_rep_update γ l l' :
  stack_rep_full γ l ==∗ stack_rep_full γ l'.
Proof.
  iApply ghost_var_update.
Qed.

Lemma stack_rep_halves_update γ l1 l2 l' :
  stack_rep_half γ l1 -∗ stack_rep_half γ l2 ==∗
  stack_rep_half γ l' ∗ stack_rep_half γ l'.
Proof.
  iApply ghost_var_update_halves.
Qed.

(** Atomic updates for push and pop *)
Definition push_au (s: loc) (v: go_string) (γ: gname) (Φ: iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ∃ l,
    stack_rep_half γ l ∗
    (stack_rep_half γ (v :: l) ={∅,⊤}=∗ Φ).

Definition pop_au (s: loc) (γ: gname) (Φ: go_string → bool → iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ∃ l,
    stack_rep_half γ l ∗
    (match l with
     | [] => stack_rep_half γ [] ={∅,⊤}=∗ Φ ""%go false
     | v::l' => stack_rep_half γ l' ={∅,⊤}=∗ Φ v true
     end).

(* Helper to convert pop postcondition to predicate format *)
Definition PopK (Φ : go_string → bool → iProp Σ) : (go_string * bool) → iProp Σ :=
  λ '(v,b), Φ v b.

(** Push token: the capability to logically push a value onto the abstract stack *)
Definition push_token (v: go_string) (γ: gname) : iProp Σ :=
  |={⊤,∅}=> ∃ l,
    stack_rep_half γ l ∗
    (stack_rep_half γ (v :: l) ={∅,⊤}=∗ True).

(** Stack invariant: protected by mutex
    Contains physical stack + push tokens for each element *)
Definition stack_inv (s: loc) (γ: stack_names) : iProp Σ :=
  ∃ (physical: list (go_string)) (slice_val: slice.t),
    "Hstack" ∷ s ↦s[(chan_spec_raw_examples.EliminationStack) :: "stack"] slice_val ∗
    "Hslice" ∷ own_slice slice_val (DfracOwn 1) physical ∗
    "Hslice_cap" ∷ own_slice_cap (go_string) slice_val (DfracOwn 1) ∗
    
    (* For each value in physical stack, we have a push token *)
    "Htokens" ∷ [∗ list] v ∈ physical, push_token v γ.(stack_state_name).

(* Exchanger invariant: the state machine for elimination *)
Definition exchanger_inv (s: loc) (ch: loc) (γ: stack_names) : iProp Σ :=
  ∃ (ch_state: chan_rep.t (go_string)),
    "chan_state" ∷ own_channel ch 0 ch_state γ.(exch_chan_name) ∗
    
    "logical" ∷ match ch_state with
      | chan_rep.Idle =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn 1) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn 1) (PopK Φpop)
      
      | chan_rep.SndPending v =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn 1) (PopK Φpop) ∗
            "push_au" ∷ push_au s v γ.(stack_state_name) Φpush
      
      | chan_rep.RcvPending =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn 1) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "pop_au" ∷ pop_au s γ.(stack_state_name) Φpop
      
      | chan_rep.SndCommit v =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "pop_complete" ∷ Φpop v true
      
      | chan_rep.RcvCommit =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "push_complete" ∷ Φpush
      
      | _ => False
      end.

Definition is_exchanger (ch: loc) (γ: stack_names) : iProp Σ :=
  is_channel ch 0 γ.(exch_chan_name).

Global Instance is_exchanger_persistent ch γ : Persistent (is_exchanger ch γ).
Proof. apply _. Qed.

Definition is_elim_stack (s: loc) (γ: stack_names) : iProp Σ :=
  ∃ (mu_loc: loc) (ch_loc: loc),
    "#mu_field" ∷ s ↦s[chan_spec_raw_examples.EliminationStack :: "mu"]□ mu_loc ∗
    "#ch_field" ∷ s ↦s[chan_spec_raw_examples.EliminationStack :: "exchanger"]□ ch_loc ∗
    "#is_lock" ∷ is_lock mu_loc (stack_inv s γ) ∗
    "#is_exchanger" ∷ is_exchanger ch_loc γ.

Global Instance is_elim_stack_persistent s γ : Persistent (is_elim_stack s γ).
Proof. apply _. Qed.

Lemma wp_NewEliminationStack :
  {{{ True }}}
  @! chan_spec_raw_examples.NewEliminationStack #()
  {{{ (s: loc) γ, RET #s; 
      is_elim_stack s γ ∗ stack_rep_full γ.(stack_state_name) []
  }}}.
Proof.
Admitted.

Lemma wp_EliminationStack__Push (s: loc) (v: go_string) (γ: stack_names):
  ∀ Φ,
  is_elim_stack s γ -∗
  push_au s v γ.(stack_state_name) (Φ #()) -∗
  WP  chan_spec_raw_examples.EliminationStack__Pushⁱᵐᵖˡ #s #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_EliminationStack__Pop (s: loc) (γ: stack_names):
  ∀ Φ,
  is_elim_stack s γ -∗
  pop_au s γ.(stack_state_name) (λ v ok, Φ (#v, #ok)%V) -∗
  WP chan_spec_raw_examples.EliminationStack__Popⁱᵐᵖˡ #s {{ Φ }}.
Proof.
Admitted.

End elim_stack.