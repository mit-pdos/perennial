From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import proofmode globals.
From New.golang.defn Require Import globals.
Import Ltac2.

(** [IsPkgInit] is used to record a mapping from pkg names to an
initialization predicate, which is the postcondition for after the package has
been initialized. This includes the package being "defined", a technicality of
Goose where function names are associated with their bodies. Defining the
package occurs prior to initializing global variables according to their
initialization expressions, as well as running init() functions.

This typeclass associates a single initialization predicate to each package,
reflecting common practice, but strictly speaking proofs could choose different
postconditions for initialization. This is similar to how almost all functions
have a canonical specification, even though they could potentially have several
incomparable ones.
*)
Class IsPkgInit (pkg_name: go_string) {PROP: bi} :=
  {
    is_pkg_init_def : PROP ;
    #[global]
    is_pkg_init_persistent :: Persistent is_pkg_init_def;
  }.

#[global]
Arguments is_pkg_init_def (pkg_name) {_ _}.
#[global]
Typeclasses Opaque is_pkg_init_def.

(* XXX: To avoid printing the IsPkgInit instances when printing [is_pkg_init]
   See https://github.com/coq/coq/issues/9814 for a description of the problem. *)
#[global]
Notation is_pkg_init := is_pkg_init_def.

#[global]
Hint Mode IsPkgInit + - : typeclass_instances.

Ltac prove_is_pkg_init :=
  constructor; refine _.

(** [IsPkgDefined] is analogous to [IsPkgInit] but looks up the
    post-definition predicate. This is something that can be auto-generated. *)
Class IsPkgDefined (pkg_name: go_string) {PROP: bi} :=
  {
    is_pkg_defined_def : PROP;
    #[global]
    is_pkg_defined_persistent :: Persistent is_pkg_defined_def;
  }.

#[global]
Arguments is_pkg_defined_def (pkg_name) {_ _}.

#[global]
Notation is_pkg_defined := is_pkg_defined_def.

#[global]
Hint Mode IsPkgDefined + - : typeclass_instances.

Ltac2 build_pkg_init () :=
  Control.refine
    (fun () =>
       lazy_match! goal with
       | [ |- IsPkgInit ?name ] =>
           let deps := Std.eval_hnf constr:(pkg_imported_pkgs $name) in
           let rec build_iprop deps :=
             lazy_match! deps with
             | cons ?pkg ?deps =>
                 let rest := build_iprop deps in
                 constr:((is_pkg_init $pkg ∗ $rest)%I)
             | nil => constr:(is_pkg_defined_def $name)
             | _ =>
                 Message.print (Message.of_constr deps);
                 Control.backtrack_tactic_failure "build_pkg_init: unable to match deps list"
             end in
           let p := build_iprop deps in
           let p := constr:(Build_IsPkgInit $name _ $p) in
           (* Intentionally leaving the `Persistent` goal unsolved so the instance can Qed it *)
           open_constr:($p _)
       | [ |- _ ] => Control.backtrack_tactic_failure "build_pkg_init: goal is not (IsPkgInit _)"
       end
    ).

(* solve a goal which is just [is_pkg_init] or [is_pkg_defined] *)
Ltac solve_pkg_init :=
  unfold named;
  lazymatch goal with
  | |- environments.envs_entails ?env (is_pkg_init _) => idtac
  | |- environments.envs_entails ?env (is_pkg_defined _) => idtac
  | _ => fail "not a is_pkg_init or is_pkg_defined goal"
  end;
  iClear "∗";
  simpl is_pkg_init;
  repeat
    lazymatch goal with
    | |- environments.envs_entails ?env _ =>
        lazymatch env with
        | context[environments.Esnoc _ ?i (_ ∗ _)%I] =>
            iDestruct i as "[? ?]"
        end
    end;
  solve [ iFrame "#" ].

(* Attempt to solve [is_pkg_init] at the front of the goal.

NOTE: The automation here is limited to match what we expect in goals and to make the
implementation simple. It is possible that the shape of expected goals changes,
for example to have multiple [is_pkg_init] conjuncts, in which case this
automation will need improvement.
*)
Ltac iPkgInit :=
  progress (
      try solve_pkg_init;
      repeat (iSplitR; [ solve_pkg_init | ])
    ).
