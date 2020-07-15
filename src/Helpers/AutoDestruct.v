From iris.proofmode Require Import tactics environments.

(*! The horrible Ltac needed to preserve binder names in
  [iDestruct "H" as (?) "H"]. *)

Ltac make_name_binder name :=
  eval cbn in (ltac:(intros name; assumption) : unit → unit).

Ltac copy_binder f :=
  lazymatch f with
  | λ x, _ => make_name_binder x
  end.

Ltac copy_binder_fallback f :=
  lazymatch f with
  | λ x, _ => make_name_binder x
  | _ => make_name_binder ident:(x)
  end.

Ltac copy_binder_to f g :=
  lazymatch f with
  | λ x, _ =>
    lazymatch type of g with
    | forall (a:?A), @?B a =>
      lazymatch g with
      | λ y, @?g_body y =>
        (* FIXME: this evaluates the body, when we just want to do one beta reduction *)
        eval cbv beta in ltac:(intros x; exact (g_body x))
      end
    end
  end.

Goal True.
  let f := copy_binder constr:(λ foo, foo + 2) in
  idtac f. (* should have foo *)
  let f := copy_binder_fallback constr:(@id nat) in
  idtac f. (* should have x *)
  let f := copy_binder_to constr:(λ (foo:unit), foo) constr:(λ bar, bar + 2) in
  idtac f. (* second function, but with foo *)
Abort.

Class IntoExistBinder {PROP : bi} {A} (P : PROP) (Φ : A → PROP) (name : unit → unit) :=
  into_exist_binder : P ⊢ ∃ x, Φ x.
Arguments IntoExistBinder {_ _} _%I _%I _ : simpl never.
Arguments into_exist_binder {_ _} _%I _%I {_} _.
Hint Mode IntoExistBinder + - ! - - : typeclass_instances.

Lemma IntoExistBinder_elim {PROP: bi} {A} P (Φ: A → PROP) name :
  IntoExistBinder P Φ name = IntoExist P Φ.
Proof. reflexivity. Qed.

Ltac into_exist :=
  lazymatch goal with
  | |- IntoExist (bi_exist (fun x => @?Φ x)) ?Φ' =>
    unify Φ Φ'; simple apply class_instances.into_exist_exist
    (* notypeclasses refine (class_instances.into_exist_exist Φ) *)
  end.

(* This is the advantage of having an additional argument: this is a regular
instance because it just forwards a name, rather than copying the name in Φ over
to the explicit function given here (which uses [a]) *)
Instance into_exist_intuinistically_binder_exist {PROP: bi} {A}
         P (Φ: A → PROP) name :
  IntoExistBinder P Φ name → IntoExistBinder (□ P) (λ a, (□ Φ a))%I name.
Proof. rewrite !IntoExistBinder_elim. apply _. Qed.

Ltac solve_IntoExistBinder :=
  rewrite !IntoExistBinder_elim; apply _.

(* into_exist_name unifies the binder in Φ with name (an evar for a unit ->
unit), then solves an IntoExist goal with typeclass resolution *)
Ltac into_exist_name Φ name :=
  let name' := copy_binder_fallback Φ in
  unify name name';
  solve_IntoExistBinder.

Ltac into_exist_binder :=
  lazymatch goal with
  | |- IntoExistBinder (bi_exist ?Φ) _ ?name =>
    let name' := copy_binder_fallback Φ in
    unify name name';
    solve_IntoExistBinder
  end.

(* this is an alternate implementation that requires every implementation of
IntoExist to carefully preserve names; in general, this is difficult because it
requires copying a binder from one IntoExist into some newly-constructed
function (using [copy_binder_to], for example) *)
Remove Hints class_instances.into_exist_exist : typeclass_instances.
Hint Extern 1 (IntoExist (bi_exist _) _) => into_exist : typeclass_instances.

(* Hint Extern 1 (IntoExistBinder (bi_exist _) _ _) => into_exist_binder : typeclass_instances. *)
(* for these two forms, we resolve name using the underlying binder in the
function *)
Hint Extern 1 (IntoExistBinder (bi_exist ?Φ) _ ?name) => into_exist_name Φ name : typeclass_instances.
Hint Extern 1 (IntoExistBinder (⌜ex ?Φ⌝)%I _ ?name) => into_exist_name Φ name : typeclass_instances.

Inductive dummy {A} (x:A) : Prop := mkDummy.
Hint Resolve mkDummy : core.

Lemma tac_exist_destruct' {PROP: bi} {A} Δ i p j P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ →
  (dummy Φ → ∀ a,
    match envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ with
    | Some Δ' => envs_entails Δ' Q
    | None => False
    end) →
  envs_entails Δ Q.
Proof.
  intros.
  eapply coq_tactics.tac_exist_destruct; eauto.
  apply H1; auto.
Qed.

Lemma tac_exist_binder_destruct' {PROP: bi} {A} Δ i p j P (Φ : A → PROP) Q name :
  envs_lookup i Δ = Some (p, P) → IntoExistBinder P Φ name →
  (dummy name → ∀ a,
    match envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ with
    | Some Δ' => envs_entails Δ' Q
    | None => False
    end) →
  envs_entails Δ Q.
Proof.
  intros.
  eapply coq_tactics.tac_exist_destruct; eauto.
  apply H1; auto.
Qed.

(* this uses the old Coq lemma, but this makes it hard to extract the Φ resolved
in the earlier hypothesis *)
Tactic Notation "iExistDestructAuto" constr(H)
    "as" constr(Hx) :=
  eapply coq_tactics.tac_exist_destruct with H _ Hx _ _; (* (i:=H) (j:=Hx) *)
    [reduction.pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoExist ?P _ => P end in
     fail "iExistDestruct: cannot destruct" P|];
    let x := lazymatch goal with
             | |- context[environments.envs_simple_replace _ _
                            (environments.Esnoc _ _ ((λ x, _) _)) _] => x
             end in
    let y := fresh in
    intros y; reduction.pm_reduce;
    match goal with
    | |- False =>
      let Hx := pretty_ident Hx in
      fail "iExistDestruct:" Hx "not fresh"
    | _ => revert y; intros x (* subgoal *)
    end.

Tactic Notation "iExistDestructAuto'" constr(H)
    "as" constr(Hx) :=
  eapply tac_exist_binder_destruct' with H _ Hx _ _ _; (* (i:=H) (j:=Hx) *)
    [reduction.pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoExistBinder ?P _ _ => P end in
     fail "iExistDestruct: cannot destruct" P|];
    let x := lazymatch goal with
             | |- dummy (λ x, _) -> _ => x
             end in
    intros _;
    let y := fresh in
    intros y; reduction.pm_reduce;
    match goal with
    | |- False =>
      let Hx := pretty_ident Hx in
      fail "iExistDestruct:" Hx "not fresh"
    | _ => revert y; intros x (* subgoal *)
    end.

Theorem test_regular_bi_exists {PROP: bi} (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ ∃ (n:nat), True.
Proof.
  iIntros "H".
  iExistDestructAuto' "H" as "H".
  iExists y; eauto.
Qed.

Theorem test_persistent_exists {PROP: bi} (Φ: nat → PROP) :
  □ (∃ y, Φ y) -∗ ∃ (n:nat), True.
Proof.
  iIntros "H".
  iExistDestructAuto' "H" as "H".
  iExists y; eauto.
Qed.

Theorem test_pure_exists {PROP: bi} (Φ: nat → Prop) :
  ⌜∃ y, Φ y⌝ ⊢@{PROP} ∃ (n:nat), True.
Proof.
  iIntros "H".
  iExistDestructAuto' "H" as "H".
  iExists y; eauto.
Qed.
