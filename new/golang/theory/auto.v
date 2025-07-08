From Perennial.goose_lang Require Import notation.
From Coq Require Import ssreflect.
From Ltac2 Require Import Ltac2 Printf.
Set Default Proof Mode "Classic".
From New.golang.defn Require Import typing.
From New.golang.theory Require Import proofmode globals pkg loop chan.
From New.golang.theory Require Import mem.
From Perennial Require Import base.

#[local] Open Scope general_if_scope.

(* TODO: iFrame # is only for backwards compatibility *)
Tactic Notation "wp_globals_get" :=
  wp_globals_get_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_func_call" :=
  wp_func_call_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_method_call" :=
  wp_method_call_core; try iPkgInit; try iFrame "#".

(* remove and introduce [is_pkg_init] and [is_pkg_defined] facts from a hypothesis *)
Ltac destruct_pkg_init H :=
  let i := lazymatch type of H with
           | string => constr:(INamed H)
           | _ => H
           end in
  let split_hyp :=
    let pat := constr:(intro_patterns.IList
                          [[intro_patterns.IIntuitionistic (intro_patterns.IFresh);
                            intro_patterns.IIdent i]]) in
    iDestruct i as pat in
  repeat
    lazymatch goal with
    | |- environments.envs_entails ?env _ =>
        lazymatch env with
        | context[environments.Esnoc _ i (is_pkg_init _ ∗ _)%I] =>
            split_hyp
        | context[environments.Esnoc _ i (is_pkg_defined _ ∗ _)%I] =>
            split_hyp
        | context[environments.Esnoc _ i (is_pkg_init _)] =>
            iDestruct i as "#?";
            iAssert emp%I with "[//]" as i
        end
    end.

(* This doesn't unfold the function being called; convenient for proving specs
   that wrap another spec. *)
Tactic Notation "wp_start_folded" "as" constr(pat) :=
  (* Sometimes a Hoare triple is used in the logic, which is an iProp with a
  persistently modality in front, unlike the top-level Hoare triple notation
  which does not require the modality.

    Ideally this tactic would differentiate these two with pattern matching but
    we haven't bothered with error messaging here.
   *)
  try (iModIntro (□ _)%I);
  (* A loop obligation might involve a new Φ but the old variable is still in
  scope. The usual pattern in our proofs is to clear the old one. *)
  let x := ident:(Φ) in
  try clear x;
  iIntros (Φ) "Hpre HΦ";
  destruct_pkg_init "Hpre";
  iDestruct "Hpre" as pat.

Tactic Notation "wp_start" "as" constr(pat) :=
  wp_start_folded as pat;
  (* only do this if it produces a single goal *)
  try (first [ wp_func_call | wp_method_call ]; wp_call; [idtac]).

Tactic Notation "wp_start" :=
  wp_start as "Hpre".

Ltac2 wp_auto_lc (num_lc_wanted : int) :=
  let num_lc_wanted := Ref.ref num_lc_wanted in
  let wp_pure_maybe_lc () :=
    if (Int.gt (Ref.get num_lc_wanted) 0) then ltac1:(wp_pure_lc "?") > []; (Ref.decr num_lc_wanted)
    else wp_pure () > []
  in
  progress (
      repeat (first [ wp_pure_maybe_lc ()
                    | wp_load ()
                    | wp_store ()
                    | wp_alloc_auto ()
                    | ltac1:(rewrite <- !default_val_eq_zero_val) ]);
      if (Int.gt (Ref.get num_lc_wanted) 0) then
        Control.backtrack_tactic_failure "wp_auto_lc: unable to generate enough later credits"
      else
        ()
    ).

(* optional parameter setup - see
https://github.com/rocq-community/rocq-tricks/blob/main/src/TacticNotationOptionalParams.v
for a detailed explanation of how this works *)
Ltac2 Type wp_param := [
  | RunAuto(bool)
  (* generate later credits *)
  | GenLc(int)
  (* intro pattern to run afterward *)
  | AsClause(Ltac1.t)
].

Ltac2 Type exn ::= [ WpParamExn(wp_param) ].

(* FIXME: setting this variable affects all imports; there doesn't seem to be a
way to set it locally *)
Ltac2 mutable wp_apply_auto_default : bool := true.

Tactic Notation "--no-auto" :=
  ltac2:(Control.zero (WpParamExn (RunAuto false))).
Tactic Notation "--auto" :=
  ltac2:(Control.zero (WpParamExn (RunAuto true))).
Tactic Notation "--lc" int(n) :=
  let f := ltac2:(n' |-
    let n := Option.get (Ltac1.to_int n') in
    Control.zero (WpParamExn (GenLc n))) in
  f n.
(* NOTE: does not support other variants of [iIntros] from
   [iris/iris/proofmode/ltac_tactics.v] to make intro patterns more canonical.
 *)
Tactic Notation "as" constr(ipat) :=
  let f := ltac2:(ipat' |-
      Control.zero (WpParamExn (AsClause ipat'))) in
  f ipat.

Ltac2 Type exn ::= [WrappedExn(message option, exn)].
Ltac2 catch_wp_param (thunk : unit -> 'a) : wp_param :=
  match Control.case thunk with
  | Val _ =>
    let msg := fprintf "No exn was thrown, so the provided parameter is invalid"
    in Control.throw (Invalid_argument (Some msg))
  | Err e =>
    match e with
    | WpParamExn p => p
    | _ =>
      let msg := fprintf "Bad exn was thrown, so the provided parameter is invalid"
      in Control.throw (WrappedExn (Some msg) e)
    end
  end.

Tactic Notation "wp_auto" tactic1_list(ps) :=
  let f := ltac2:(ps_raw |-
    let r_lc := Ref.ref 0 in
    let ps : Ltac1.t list := Option.get (Ltac1.to_list ps_raw) in
    List.iter (fun p =>
      let param := catch_wp_param (fun () => Ltac1.run p) in
      match param with
      | GenLc n => Ref.set r_lc n
      | _ =>
          let msg := fprintf "Unexpected argument to wp_auto" in
          Control.throw (Invalid_argument (Some msg))
      end
    ) ps;
    wp_auto_lc (Ref.get r_lc)
  ) in
  f ps.

(* TODO: move this general-purpose Ltac2 infrastructure out *)
Ltac2 focus_last0 (t: unit -> 'a) : 'a :=
  let n := Control.numgoals () in
  if Int.equal n 0 then ()
  else Control.focus n n t.

(* equivalent of ssreflect last *)
Ltac2 Notation focus_last := focus_last0.

(* TODO: centralize Ltac2 wrappers (which are useful for building Ltac2
automation) *)
Ltac2 wp_apply_core (lem: Ltac1.t) : unit :=
  ltac1:(lem |- wp_apply_core lem) lem.

Ltac2 iIntros (ipat: Ltac1.t) : unit :=
  ltac1:(ipat |- iIntros ipat) ipat.

Ltac2 wp_apply (lem: Ltac1.t) (do_auto: bool) (lc: int) (as_clause: Ltac1.t option) :=
    wp_apply_core lem; try ltac1:(iPkgInit);
    match as_clause with
    | Some ipat => focus_last (iIntros ipat)
    | None => ()
    end;
    if do_auto then
      focus_last (try (wp_auto_lc lc))
      else ().

Tactic Notation "wp_apply" open_constr(lem) tactic1_list(ps) :=
  let f := ltac2:(lem ps_raw |-
    let r_auto := Ref.ref wp_apply_auto_default in
    let r_lc := Ref.ref 0 in
    let r_as: (Ltac1.t option) Ref.ref := Ref.ref None in
    let ps : Ltac1.t list := Option.get (Ltac1.to_list ps_raw) in
    List.iter (fun p =>
      let param := catch_wp_param (fun () => Ltac1.run p) in
      match param with
      | GenLc n => Ref.set r_lc n
      | AsClause ipat => Ref.set r_as (Some ipat)
      | RunAuto b => Ref.set r_auto b
      end
    ) ps;
    wp_apply lem (Ref.get r_auto) (Ref.get r_lc) (Ref.get r_as)
  ) in
  f lem ps.

(* NOTE: this could be refined to give helpful errors when auto gets stuck by
   using the [Tactic_failure] exception under the hood for backtracking, but using
   some new exception [Human_input_needed] which causes [wp_auto] to stop
   backtracking and to immediately report to the user.
 *)
Tactic Notation "wp_auto_lc" int(x) :=
  let f := ltac2:(x |- wp_auto_lc (Option.get (Ltac1.to_int x))) in
  f x.

Lemma if_decide_bool_eq_true `{!ffi_syntax} {A} `{!Decision P} (x y: A) :
  (if decide (#(bool_decide P) = #true) then x
  else y) = (if bool_decide P then x else y).
Proof.
  destruct (bool_decide_reflect P).
  - rewrite decide_True //.
  - rewrite decide_False //.
    inv 1.
Qed.

Lemma if_decide_bool_eq_false `{!ffi_syntax} {A} `{!Decision P} (x y: A) :
  (if decide (#(bool_decide P) = #false) then x
  else y) = (if bool_decide P then y else x).
Proof.
  destruct (bool_decide_reflect P).
  - rewrite decide_False //.
    inv 1.
  - rewrite decide_True //.
Qed.

(* This simplifies the postcondition in the subgoal generated by [wp_for] for
the common case where the value produced is a [bool_decide] expression (which is
how GooseLang should work). I'm not sure how to integrate this into automation,
since this only comes up after reasoning about the loop condition. *)
Lemma if_decide_bool_eq `{!ffi_syntax} {A} `{!Decision P} (x y z: A) :
  (if decide (#(bool_decide P) = #true) then x
  else if decide (#(bool_decide P) = #false) then y
      else z) = (if bool_decide P then x else y).
Proof.
  rewrite if_decide_bool_eq_true.
  destruct (bool_decide_reflect P); auto.
  rewrite decide_True //.
Qed.

(* This patterns comes up in the postcondition from [wp_for] if the condition is
the constant [#true] (for infinite loops using [break] for example) *)
Lemma if_decide_true_eq `{!ffi_syntax} {A} (x y: A) :
  (if decide (#true = #true) then x else y) = x.
Proof.
  rewrite decide_True //.
Qed.

Ltac cleanup_bool_decide :=
  rewrite ?if_decide_bool_eq_true ?if_decide_bool_eq_false ?if_decide_true_eq.

#[local]
Ltac wp_for_cleanup :=
  try wp_auto;
  cleanup_bool_decide;
  try wp_auto.

Tactic Notation "wp_for" :=
  loop.wp_for_core; wp_for_cleanup.
Tactic Notation "wp_for" constr(hyp) :=
  loop.wp_for_core; iNamed hyp; wp_for_cleanup.
Ltac wp_for_post :=
  loop.wp_for_post_core; try wp_auto.

Tactic Notation "wp_for_chan" :=
  chan.wp_for_chan_core; wp_for_cleanup.
Tactic Notation "wp_for_chan" constr(hyp) :=
  chan.wp_for_chan_core; iNamed hyp; wp_for_cleanup.
Ltac wp_for_chan_post :=
  chan.wp_for_chan_post_core; try wp_auto.

(* TODO: one tactic to handle all for loops. *)


(* TODO: this is a very basic implementation that would benefit from
post-processing. This is because bool_decide can come with some complications
that should be simplified, like negb around bool_decide or equality of values
inside the bool_decide. *)
Ltac wp_if_destruct :=
  lazymatch goal with
  | |- environments.envs_entails _ ?g =>
      match g with
      | context[bool_decide ?b] =>
          destruct (bool_decide_reflect b); subst;
          wp_pures;
          cleanup_bool_decide
      end
  end.
