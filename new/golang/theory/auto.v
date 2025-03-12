From Perennial.goose_lang Require Import notation.
Import Ltac2.
From New.golang.theory Require Import proofmode mem globals pkg loop.
From Coq Require Import Strings.Ascii.

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

Tactic Notation "wp_start" "as" constr(pat) :=
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
  iDestruct "Hpre" as pat;
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
                    | wp_alloc_auto ()]);
      if (Int.gt (Ref.get num_lc_wanted) 0) then
        Control.backtrack_tactic_failure "wp_auto_lc: unable to generate enough later credits"
      else
        ()
    ).

(* NOTE: this could be refined to give helpful errors when auto gets stuck by
   using the [Tactic_failure] exception under the hood for backtracking, but using
   some new exception [Human_input_needed] which causes [wp_auto] to stop
   backtracking and to immediately report to the user.
 *)
Tactic Notation "wp_auto" := ltac2:(wp_auto_lc 0).
Tactic Notation "wp_auto_lc" int(x) :=
  let f := ltac2:(x |- wp_auto_lc (Option.get (Ltac1.to_int x))) in
  f x.

Tactic Notation "wp_apply_lc" int(n) open_constr(lem) :=
  wp_apply_core lem; try iPkgInit;
  try (let f := ltac2:(n |- wp_auto_lc (Option.get (Ltac1.to_int n))) in f n).

(* NOTE: did not copy in other variants of [iIntros] from [iris/iris/proofmode/ltac_tactics.v] to
   make intro patterns more canonical.
 *)
Tactic Notation "wp_apply_lc" int(n) open_constr(lem) "as" constr(pat) :=
  wp_apply_core lem; try iPkgInit;
  last (iIntros pat; try (let f := ltac2:(n |- wp_auto_lc (Option.get (Ltac1.to_int n))) in f n)).

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_lc 0 lem.

Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply_lc 0 lem as pat.

#[local]
Ltac wp_for_cleanup :=
  try wp_auto;
  try (rewrite if_decide_bool_eq || rewrite if_decide_true_eq);
  try wp_auto.

Tactic Notation "wp_for" :=
  loop.wp_for_core; wp_for_cleanup.
Tactic Notation "wp_for" constr(hyp) :=
  loop.wp_for_core; iNamed hyp; wp_for_cleanup.
Ltac wp_for_post :=
  loop.wp_for_post_core; try wp_auto.
