From iris.proofmode Require Import tactics environments.

(*! The horrible Ltac needed to preserve binder names in
  [iDestruct "H" as (?) "H"]. *)

Ltac copy_binder f :=
  lazymatch f with
  | λ x, _ => eval cbn in (ltac:(intros x; assumption) : unit -> unit)
  end.

Goal True.
  let f' := copy_binder constr:(λ foo, foo + 2) in
  idtac f'.
Abort.

Ltac into_exist :=
  lazymatch goal with
  | |- IntoExist (bi_exist (fun x => @?Φ x)) ?Φ' =>
    unify Φ Φ'; apply class_instances.into_exist_exist
    (* notypeclasses refine (class_instances.into_exist_exist Φ) *)
  end.

Remove Hints class_instances.into_exist_exist : typeclass_instances.
Hint Extern 1 (IntoExist (bi_exist _) _) => into_exist : typeclass_instances.

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
  eapply tac_exist_destruct' with H _ Hx _ _; (* (i:=H) (j:=Hx) *)
    [reduction.pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoExist ?P _ => P end in
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

Theorem foo {PROP: bi} (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ True.
Proof.
  iIntros "H".
  iExistDestructAuto' "H" as "H".
Abort.

Theorem bar {PROP: bi} (Φ: nat → PROP) :
  □ (∃ y, Φ y) -∗ True.
Proof.
  iIntros "H".
  iExistDestructAuto' "H" as "H".
Abort.
