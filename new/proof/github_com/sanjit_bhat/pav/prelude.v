(* usage: before importing this, import anything you want.
after importing this, don't import anything except "new/proof" files,
which shouldn't have side-effects (including Exports)
or unintended name shadows. *)

(* for inG's. not exported. *)
From New.proof Require Import proof_prelude.
From New.proof Require Import sync.

(* add extra dependencies. *)
From RecordUpdate Require Export RecordSet.
From iris_named_props Require Export custom_syntax.
From Perennial.Helpers Require Export bytes condition Map.
From iris.base_logic.lib Require Export mono_nat ghost_map.
From Perennial.base_logic Require Export mono_list.

(* set the right shadowed dependencies. *)
(* note: stdpp overrides some Stdlib names. *)
From stdpp Require Export prelude.
From Perennial.algebra Require Export ghost_var.

(* restore perennial's side-effects. *)
Ltac obligation_tac :=
  try
    match goal with
    | |- seal _ => eexists; reflexivity
    | _ => solve [ apply _ ]
    end.
#[global] Obligation Tactic := obligation_tac.
#[export] Set Default Goal Selector "!".
#[global] Open Scope Z_scope.

(* inG's. maybe this should go in separate file. *)
Class sigpredG Σ := {
  (* ghost_var of vrfPk. *)
  #[global] sigpredG_vrf :: ghost_varG Σ (list w8);
  (* ghost_var of audit start epoch. *)
  #[global] sigpredG_startEp :: ghost_varG Σ w64;
  (* mono_list of audited links. *)
  #[global] sigpredG_chain :: mono_listG (list w8) Σ;
}.

Class pavG Σ := {
  #[global] pavG_sigpred :: sigpredG Σ;
  (* serverσ.hist. *)
  #[global] pavG_serv_hist :: mono_listG (list w8 * (gmap w64 (list $ list w8))) Σ;
  (* serverσ.pending. each uid has a mono_list of (ver, pk). *)
  #[global] pavG_serv_uids :: mono_listG (w64 * list w8) Σ;
  #[global] pavG_sync :: syncG Σ;
}.

(* misc. TODO: these should definitely go into separate file. *)

Definition option_bool {A} (mx : option A) :=
  match mx with None => false | _ => true end.

Section misc.
Context {PROP : bi} `{!BiFUpd PROP}.

(* this helps proving [BlameSpec] when we need to open invs
after learning that a party is good. *)
Lemma fupd_not_prop P `{Decision P} : (⌜P⌝ ={⊤}=∗ False : PROP) ⊢ |={⊤}=> ¬ ⌜P⌝.
Proof.
  iIntros "H".
  destruct (decide P); [|done].
  by iMod ("H" with "[//]").
Qed.
End misc.
