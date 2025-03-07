From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import proofmode mem globals pkg.
From Coq Require Import Strings.Ascii.

(* TODO: iFrame # is only for backwards compatibility *)
Tactic Notation "wp_globals_get" :=
  wp_globals_get_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_func_call" :=
  wp_func_call_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_method_call" :=
  wp_method_call_core; try iPkgInit; try iFrame "#".

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem; try iPkgInit.

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

(* string $ prefix to create valid Coq identifiers *)
Definition clean_ident (s: string): string :=
  match s with
  | String "$"%char s' => s'
  | _ => s
  end.

(* Use the Go variable name to automate calling wp_alloc. A variable called "x"
will get a location variable x_l (in Gallina) and a spatial hypothesis "x" for
the points-to. *)
Ltac wp_alloc_auto :=
  match goal with
    (* matches (exception_do (let: ?v := _ in _)), but this has to be written
    out since we don't have function coercions being inserted *)
  | |- context[(WP (App (Val exception.exception_do)
                      (App (Rec BAnon (BNamed ?v) _) _)%E) {{ _ }})%I ] =>
      let i := (eval compute in (clean_ident v)) in
      string_ident.string_to_ident_cps i
        ltac:(fun x => let x_l := fresh x "_l" in
                       wp_alloc x_l as i
             )
  end.

Ltac wp_auto := repeat first [ progress wp_pures
                             | wp_load
                             | wp_store
                             | wp_alloc_auto ].
