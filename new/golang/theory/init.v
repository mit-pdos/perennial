From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import proofmode globals.
From New.golang.defn Require Import globals.

(** PkgIsInitialized is used to record a mapping from pkg names to an
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
Class PkgIsInitialized (pkg_name: go_string) {PROP: bi} (initP: PROP) :=
  { init_persistent :: Persistent initP; }.

#[global]
Hint Mode PkgIsInitialized + - - : typeclass_instances.

Ltac prove_pkg_is_initialized :=
  constructor; refine _.

(** [is_pkg_init pkg] gets the package's initialization predicate via the
[PkgInitialized] typeclass *)
Definition is_pkg_init (pkg_name: go_string) {PROP: bi} {initP: PROP}
  `{!PkgIsInitialized pkg_name initP}: PROP := initP.

(** [PkgIsDefined] is analogous to [PkgIsInitialized] but looks up the
post-definition predicate. This is something that can be auto-generated. *)
Class PkgIsDefined (pkg_name: go_string) {PROP: bi} (definedP: PROP) :=
  { defined_persistent :: Persistent definedP; }.

#[global]
Hint Mode PkgIsDefined + - - : typeclass_instances.

Ltac prove_pkg_is_defined :=
  constructor; refine _.

(** [is_pkg_init pkg] looks up the package's definedness predicate *)
Definition is_pkg_defined (pkg_name: go_string) {PROP: bi} {definedP: PROP}
  `{!PkgIsDefined pkg_name definedP}: PROP := definedP.

Ltac build_pkg_init_cps deps_list base rx :=
  lazymatch deps_list with
  | cons ?pkg ?deps_list' =>
      build_pkg_init_cps deps_list' base
        ltac:(fun initP' => rx (is_pkg_init pkg ∗ initP')%I)
  | nil => rx base
  end.

Ltac basic_pkg_init :=
  match goal with
  | |- PkgIsInitialized ?name _ =>
      let deps := (eval hnf in (pkg_imported_pkgs name)) in
      build_pkg_init_cps deps uconstr:(is_pkg_defined name) ltac:(fun P =>
        apply (Build_PkgIsInitialized name _ P);
        refine _
        )
  end.

Ltac iPkgInit :=
  unfold named;
  lazymatch goal with
  | |- environments.envs_entails ?env (is_pkg_init _) => idtac
  | |- environments.envs_entails ?env (is_pkg_defined _) => idtac
  | _ => fail "not a is_pkg_init or is_pkg_defined goal"
  end;
  iClear "∗";
  unfold is_pkg_init;
  repeat
    lazymatch goal with
    | |- environments.envs_entails ?env _ =>
        lazymatch env with
        | context[environments.Esnoc _ ?i (_ ∗ _)%I] =>
            iDestruct i as "[? ?]"
        end
    end;
  solve [ iFrame "#" ].
