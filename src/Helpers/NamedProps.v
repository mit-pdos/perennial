From iris.proofmode Require Import string_ident.
From iris.proofmode Require Import tactics environments intro_patterns.

Set Default Proof Using "Type".

(* NamedProps implements [named name P], which is equivalent to P but knows to
   name itself [name] when iIntro'd. The syntax looks like [name ∷ P], in
   analogy to in Gallina where you might write [forall (Hfoo: 3 < 4), ...] for a
   hypothesis that would be introduced as `Hfoo` using automatic names.

  To use this library, write your definitions with [name ∷ P] for each conjunct.
  Then, use [iNamed "H"] to destruct an invariant "H" into its conjuncts, using
  their specified names. [iNamed] also introduces existentials with the names
  for the Coq binders.

  The names in a [named] are not actually names but full-blown Iris intro
  patterns. This means you can write [#H] to automatically introduce to the
  persistent context, [%H] to name a pure fact (using string_to_ident), or even
  something crazy like ["[<- H]"] to destruct the hypothesis and rewrite by the
  first conjunct.

  There are a few more top-level tactics provided to work with named
  propositions:
  - [iNamed] names any anonymous hypotheses (without destructing them)
  - [iNamed 1] on a wand introduces and destructs the premise.
  - [iNamedAccu] is like [iAccu] - it solves a goal which is an evar with the
    conjunction of all the hypotheses - but produces a conjunction of named
    hypotheses. This is especially useful when that evar ?Q shows up as a
    premise in a wand, [?Q -∗ ...], at which point you can do [iNamed 1] to
    restore the context, including all the names.
  - [iFrameNamed] is a work-in-progress tactic to frame a goal with named
    conjuncts with the hypotheses using the names. This is intended to be much
    faster than framing the entire persistent and spatial contexts.

  Note that this library provides general support for propositions and is not
  specific to definitions. You can use named hypotheses in Hoare logic
  preconditions (to make the first iIntros more stable), in the postcondition
  (to make it easier for the caller to re-introduce hypotheses), or in loop
  invariants (to serve both of these purposes). If they ever get in the way you
  can always [rewrite /named] to get rid of the names.
 *)

(* Named props are just the underlying prop. We used to have this sealed, but it
turns out that this inconveniently required many forwarding typeclass instances
(for things like [IntoPure], [Persistent], and framing) and we didn't run into
any issues making it completely transparent.

For efficiency reasons, don't even bother requiring P to be a PROP (this
introduces an extra coercion to the carrier) *)
Definition named {A} (name: string) (P: A): A := P.

Section named.
  Context {PROP:bi}.

  Theorem to_named name (P: PROP) : P -∗ named name P.
  Proof. auto. Qed.
  Theorem from_named name (P: PROP) : named name P -∗ P.
  Proof. auto. Qed.

  (* implementation of [iNamedAccu]; the soundness proof basically shows these
  definitions are equivalent to the ones used in the [iAccu] implementation,
  since we can simply unfold [named, since we can simply unfold [named]] *)

  Fixpoint env_to_named_prop_go (acc : PROP) (Γ : env PROP) : PROP :=
    match Γ with
    | Enil => acc
    | Esnoc Γ (INamed name) P => env_to_named_prop_go (named name P ∗ acc)%I Γ
    | Esnoc Γ _ P => env_to_named_prop_go (named "?" P ∗ acc)%I Γ
    end.
  Definition env_to_named_prop (Γ : env PROP) : PROP :=
    match Γ with
    | Enil => emp%I
    | Esnoc Γ (INamed name) P => env_to_named_prop_go (named name P) Γ
    | Esnoc Γ _ P => env_to_named_prop_go (named "?" P) Γ
    end.

  Theorem env_to_named_prop_go_unname (acc: PROP) Γ :
    env_to_named_prop_go acc Γ = env_to_prop_go acc Γ.
  Proof.
    revert acc.
    induction Γ; simpl; auto; intros.
    rewrite IHΓ.
    destruct i; simpl; auto.
  Qed.

  Theorem env_to_named_prop_unname (Γ: env PROP) :
    env_to_named_prop Γ = env_to_prop Γ.
  Proof.
    destruct Γ; auto.
    destruct i; simpl; rewrite env_to_named_prop_go_unname //.
  Qed.

  Theorem env_to_named_prop_sound (Γ: env PROP) :
    env_to_named_prop Γ ≡ ([∗] Γ)%I.
  Proof.
    rewrite env_to_named_prop_unname env_to_prop_sound //.
  Qed.

  Lemma tac_named_accu Δ (P: PROP) :
    env_to_named_prop (env_spatial Δ) = P →
    envs_entails Δ P.
  Proof.
    rewrite env_to_named_prop_unname.
    apply coq_tactics.tac_accu.
  Qed.

End named.

Ltac to_pm_ident H :=
  lazymatch type of H with
  | string => constr:(INamed H)
  | ident => constr:(H)
  end.

Local Ltac iDeex_as i x :=
  let x' := fresh x in
  iDestructHyp i as (x') i.

Ltac iDeex :=
  repeat match goal with
         | |- context[Esnoc _ ?i (bi_exist (fun x => _))] =>
           iDeex_as i x
         end.

(** [IsExistential] identifies propositions that should be destructed as
existentials by [iDeex]. *)
Class IsExistential {PROP:bi} (P: PROP) := is_existential {}.
Arguments is_existential {PROP P} : assert.
Instance is_existential_exist {PROP:bi} {A} (Φ: A → PROP) :
  IsExistential (bi_exist Φ).
Proof. Qed.

(** [IsSplittable] identifies separating conjunction-like propositions that
should be split by [iNamed] as it traverses a proposition for named conjuncts.
*)
Class IsSplittable {PROP:bi} (P: PROP) := is_splittable {}.
Arguments IsSplittable {_} _%I : assert.
Arguments is_splittable {PROP P} : assert.
Instance is_splittable_sep {PROP:bi} (P Q: PROP) :
  IsSplittable (P ∗ Q).
Proof. Qed.

(** tc_is_inhabited succeeds if P is an inhabited typeclass and fails otherwise.
*)
Ltac tc_is_inhabited P :=
  first [ let _ := constr:(ltac:(iSolveTC) : P) in idtac
        | fail 1 "could not satisfy" P ].

Ltac iDeex_one H :=
  lazymatch iTypeOf H with
  | Some (_, ?P) => lazymatch P with
                    | named _ _ => idtac
                    | _ => tc_is_inhabited (IsExistential P);
                           iDestruct H as (?) H
                    end
  | None => fail 1 "iDeexHyp:" H "not found"
  end.

(* iDeexHyp is like [iDestruct "H" as (?) "H"] except that it preserves the name
of the binder and repeats while the goal is an existential *)
Ltac iDeexHyp H :=
  iDeex_one H; repeat iDeex_one H.

Lemma tac_name_replace {PROP:bi} (i: ident) Δ p (P: PROP) Q name :
  envs_lookup i Δ = Some (p, named name P) →
  match envs_simple_replace i p (Esnoc Enil (INamed name) P) Δ with
  | Some Δ' => envs_entails Δ' Q
  | None => False
  end →
  envs_entails Δ Q.
Proof. rewrite /named. apply coq_tactics.tac_rename. Qed.

Local Ltac iNameReplace i name :=
  eapply (tac_name_replace i _ _ _ _ name);
  [ first [ reduction.pm_reflexivity
          | fail 1 "iNamed: could not find" i ]
  | reduction.pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "iNamed: name in not fresh" i
    | _ => idtac
    end
  ].

Lemma tac_name_intuitionistic {PROP:bi} Δ i i' p (P P' Q: PROP) name :
  envs_lookup i Δ = Some (p, named name P) →
  IntoPersistent p P P' →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  match envs_replace i p true (Esnoc Enil i' P') Δ with
  | Some Δ' => envs_entails Δ' Q
  | None => False
  end →
  envs_entails Δ Q.
Proof.
  rewrite /named.
  rewrite envs_entails_eq => ? HP' HPQ HQ.
  destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_replace_singleton_sound //.
  rewrite HQ.

  destruct p; simpl.
  - iIntros "[#HP HQ]".
    iApply "HQ".
    iApply "HP".
  - iIntros "[#HP HQ]".
    iApply "HQ"; iFrame "#".
Qed.

Local Ltac iNameIntuitionistic i i' :=
  eapply (tac_name_intuitionistic _ i i' _ _ _ _ _);
  [ reduction.pm_reflexivity
  | iSolveTC
  | simpl; iSolveTC
  | reduction.pm_reduce
  ].

Local Ltac iNamePure i name :=
  let id := string_to_ident name in
  let id := fresh id in
  iPure i as id.

(* iNameHyp implements naming a hypothesis of the form [H: name ∷ P].

   The complete tactic is mutually recursive with iNamed_go for * patterns; this
   self-contained version takes iNamed_go as a parameter *)
Local Ltac iNameHyp_go_rx H iNamed_go :=
  let i := to_pm_ident H in
  lazymatch goal with
  | |- context[Esnoc _ i (named ?name ?P)] =>
    (* we check for some simple special-cases: *)
    let pat := intro_pat.parse_one name in
    lazymatch pat with
    | IIdent (INamed ?name) =>
      (* just rename one hypothesis *)
      iNameReplace i name
    | IIntuitionistic (IIdent ?i') =>
      iNameIntuitionistic i i'
    (* pure intros need to be freshened (otherwise they block using iNamed) *)
    | IPure (IGallinaNamed ?name) =>
      iNamePure i name
    (* the token "*" causes iNamed to recurse *)
    | IForall => change (Esnoc ?Δ i (named name P)) with (Esnoc Δ i P); iNamed_go i
    | _ =>
       (* we now do this only for backwards compatibility, which is a completely
       safe but inefficient sequence that handles persistent/non-persistent
       things correctly (most likely few patterns not covered above should even
       be supported) *)
       let Htmp := iFresh in
       iRename i into Htmp;
       iDestruct (from_named with Htmp) as pat;
       try iClear Htmp
    end
  | |- context[Esnoc _ i _] =>
    fail "iNameHyp: hypothesis" H "is not a named"
  | _ => fail 1 "iNameHyp: hypothesis" H "not found"
  end.

(* The core of iNamed is destructing a spine of separating conjuncts and naming
  each conjunct with iNameHyp; the implementation currently just calls iDestruct
  and then attempts to name the new anonymous hypotheses, but it would be better
  to parametrize the splitting and naming into a typeclass. *)
Ltac iNamedDestruct_go_rx H iNameHyp :=
  (* we track the original name H0 here so that at the very end we can name the
  last conjunct if it isn't named (this is what PropRestore runs into - it can
  be destructed until a final Restore hypothesis) *)
  let rec go H0 H :=
      first [ iNameHyp H
            | lazymatch iTypeOf H with
              | Some (_, ?P) => tc_is_inhabited (IsSplittable P)
              | None => fail 1 "iNamed: hypothesis" H "not found"
              end;
              let Htmp1 := iFresh in
              let Htmp2 := iFresh in
              let pat := constr:(IList [[IIdent Htmp1; IIdent Htmp2]]) in
              iDestruct H as pat;
              iNameHyp Htmp1; go H0 Htmp2
            | (* reaching here means the last conjunct could not be named with
              iNameHyp; rather than leave it anonymous, restore the original
              name (note this could fail if that name was used by one of the
              inner names, which we don't handle here) *)
              iRename H into H0 ] in
  go H H.

(* this declaration defines iNamed by tying together all the mutual recursion *)
Local Ltac iNamed_go H :=
  lazymatch H with
  | 1%Z => let i := iFresh in iIntros i; iNamed_go i
  | 1%nat => let i := iFresh in iIntros i; iNamed_go i
  | _ =>
    (* first destruct the existentials, then split the conjuncts (but
    importantly only these two levels; the user must explicitly opt-in to
    destructing more existentials for conjuncts) *)
    try iDeexHyp H;
    iNamedDestruct_go H
  end with
  (* Ltac *) iNameHyp_go H :=
  iNameHyp_go_rx H iNamed_go with
  (* Ltac *) iNamedDestruct_go H := iNamedDestruct_go_rx H iNameHyp_go.

Tactic Notation "iNamedDestruct" constr(H) := iNamedDestruct_go H.
Tactic Notation "iNamed" constr(H) := iNamed_go H.

(* iNamed names any hypotheses that are anonymous but have a name. This is
primarily useful when you for some reason need to introduce using ? and then
separately name (this can arise if [iNamed] isn't doing the right thing, or
wouldn't work for all the conjuncts) *)
Tactic Notation "iNamed" :=
  repeat match goal with
         | |- context[Esnoc _ ?i (named ?name ?P)] =>
           iNameHyp_go i
         (* TODO: debug this for destructing anonymous composites *)
         (* | |- context[Esnoc _ ?i ?P] =>
           lazymatch P with
           | context[named _ _] => progress iNamed i
           end *)
         end.

(* iNameHyp only introduces names for a single hypothesis (and is usually not
useful on its own) *)
Ltac iNameHyp H := iNameHyp_go H.

Tactic Notation "iNamedAccu" :=
  iStartProof; eapply tac_named_accu; [ (* only one goal should spawn *)
    first [
        cbv [ env_to_named_prop env_to_named_prop_go ];
        reduction.pm_reflexivity
      | fail 1 "iNamedAccu: not an evar"
      ]
  ].

Ltac iRed :=
  lazymatch goal with
  | [ |- envs_entails _ ?g ] =>
    let g' := (eval red in g) in
    change_no_check g with g'
  end.

Ltac iHnf :=
  lazymatch goal with
  | [ |- envs_entails _ ?g ] =>
    let g' := (eval hnf in g) in
    change_no_check g with g'
  end.

Ltac iFrameNamed :=
  lazymatch goal with
  | [ |- envs_entails _ ?g ] =>
    repeat match g with
           | context[named ?p ?P] =>
             let pat := intro_patterns.intro_pat.parse_one p in
             lazymatch pat with
             | IIdent ?name => iFrame name
             | IIntuitionistic (IIdent ?name) => iFrame name
             | IPure (IGallinaNamed ?name) =>
               let name := string_to_ident name in
               iFrame (name)
             end
           end
  end.

Ltac prove_named :=
  iEval (rewrite /named).

(* this is crucially placed just below level 80, which is where ∗ is, so that
you can change [P ∗ Q] to ["HP" ∷ P ∗ "HQ" ∷ Q] without adding parentheses to
attach the names correctly *)
Notation "name ∷ P" := (named name P%I) (at level 79).

(* Enable eauto to solve goals where the top-level is [named] *)
Hint Extern 0 (environments.envs_entails _ (named _ _)) => unfold named : core.

(* TODO: maybe we should move tests out *)
Module tests.
  Set Default Proof Using "All".
  Section tests.
    Context {PROP: bi} {Haffine: BiAffine PROP}.
    Implicit Types (P Q R : PROP).
    Implicit Types (Ψ: nat -> PROP).
    Implicit Types (φ: Prop).

    Example test_name_named_1 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q.
    Proof.
      iIntros "? ?".
      iNamed.
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
    Qed.

    Example test_name_named_2 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q%I.
    Proof.
      iIntros "H₁ H₂".
      iNameHyp "H₁".
      iNameHyp "H₂".
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
    Qed.

    Example test_pure_pattern_freshen φ φ' P :
      named "%H" ⌜φ⌝ -∗
      named "%H" ⌜φ'⌝ -∗
      P -∗
      ⌜φ ∧ φ'⌝ ∗ P.
    Proof.
      iIntros "H1 H2 $".
      iNameHyp "H1".
      iNameHyp "H2".
      iPureIntro; exact (conj H H0).
    Qed.

    Example test_destruct_named P Q :
      ⊢ named "H1" P ∗
        named "H2" Q ∗
        named "H3" P ∗
        named "H4" Q
        -∗
        P ∗ Q ∗ P ∗ Q.
    Proof.
      iIntros "H".
      iNamedDestruct "H".
      iFrame.
    Qed.

    Example test_destruct_pat (foo: Prop) P Q :
      ⊢ named "[%Hfoo HP]" (⌜foo⌝ ∗ P) ∗
        named "HQ" Q ∗
        named "HP2" P
        -∗
        ⌜foo⌝ ∗ P ∗ Q ∗ P.
    Proof.
      iIntros "H".
      iNamedDestruct "H".
      iFrame "HP HQ HP2".
      iPureIntro; exact Hfoo.
    Qed.

    Example test_frame_named P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      iFrame "HQ HP".
    Qed.

    Example test_frame_named_sep P Q :
      ⊢ P -∗ Q -∗ named "HPQ" (P ∗ Q).
    Proof.
      iIntros "HP HQ".
      iFrame.
    Qed.

    Example test_remove_named_in_goal P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      prove_named.
      iFrame.
    Qed.

    Example test_exist_destruct Ψ Q :
      ⊢ (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q) -∗ (∃ x, Ψ x) ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      iSplitL "HP"; [ iExists x | ]; iFrame.
    Qed.

    Definition rep_invariant Ψ Q : PROP :=
      (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q)%I.

    Example test_exist_destruct_under_definition Ψ Q :
      ⊢ rep_invariant Ψ Q -∗ (∃ x, Ψ x) ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      iSplitL "HP"; [ iExists x | ]; iFrame.
    Qed.

    Example test_exist_destruct_no_naming Ψ Q :
      ⊢ (∃ x, Ψ x) -∗ (∃ x, Ψ x).
    Proof.
      iIntros "H".
      iNamed "H".
      iExists x; iFrame "H".
    Qed.

    Example test_multiple_exist_destruct Ψ Q :
      ⊢ (∃ x y z, Ψ (x + y + z)) -∗ (∃ x, Ψ x).
    Proof.
      iIntros "H".
      iNamed "H".
      iExists (x+y+z); iFrame "H".
    Qed.

    Example test_iNamed_destruct_pat φ P Q :
      ⊢ named "[%Hfoo HP]" (⌜φ⌝ ∗ P) ∗
        named "HQ" Q ∗
        named "HP2" P
        -∗
        ⌜φ⌝ ∗ P ∗ Q ∗ P.
    Proof.
      iIntros "H".
      iNamed "H".
      iFrame "HP HQ HP2".
      iPureIntro; exact Hfoo.
    Qed.

    Example test_named_into_pure φ Q :
      named "N" ⌜φ⌝ ∗ Q -∗ Q.
    Proof.
      iIntros "[%HP HQ]".
      iFrame.
    Qed.

    Example test_named_persistent P :
      named "#H" (□P) -∗ □P.
    Proof.
      iIntros "HP".
      iNamed "HP".
      iModIntro.
      iExact "H".
    Qed.

    Example test_named_persistent_same_name P :
      named "#H" (□P) -∗ □P.
    Proof.
      iIntros "H".
      iNamed "H".
      iModIntro.
      iExact "H".
    Qed.

    Example test_named_persistent_conjuncts P Q :
      named "#H" (□P) ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
    Proof.
      iIntros "H".
      iDestruct "H" as "[Htmp1 H]".
      iNamed "H".
      auto.
    Qed.

    Example test_named_persistent_context P Q :
      named "#H" (□P) ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
    Proof.
      iIntros "#HQ".
      iNamed "HQ".
      auto.
    Qed.

    Example test_named_already_persistent `{!Persistent P} Q :
      named "#H" P ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      auto.
    Qed.

    Example test_named_last_not_named P Q :
      named "HP" P ∗ Q -∗ P ∗ Q.
    Proof.
      iIntros "HQ".
      iNamed "HQ".
      iSplitR "HQ"; iAssumption.
    Qed.

    Example test_named_from_pure φ Q :
      φ ->
      Q -∗ Q ∗ named "N" ⌜φ⌝.
    Proof.
      iIntros (HP) "HQ".
      iFrame.
      iPureIntro.
      done.
    Qed.

    Example test_named_not_found P :
      named "HP" P -∗ P.
    Proof.
      iIntros "HP".
      Fail iNamed "foo". (* hypothesis "foo" not found *)
      iNamed "HP".
      iExact "HP".
    Qed.

    Example test_exists Ψ :
      named "HP2" (∃ my_name, Ψ my_name) -∗
      named "HP" (∃ x, Ψ x).
    Proof.
      iIntros "?"; iNamed.
      iDeexHyp "HP2".
      iExists my_name; iFrame.
    Qed.

    Example test_exists_freshen x Ψ :
      named "HP" (Ψ x) -∗ named "HP2" (∃ x, Ψ x) -∗
      named "HP" (∃ x, Ψ x).
    Proof.
      iIntros "? ?"; iNamed.
      iDeexHyp "HP2".
      iExists x0; iFrame.
    Qed.

    Definition simple_rep P := "HP" ∷ P.

    (* TODO: this is a bug *)
    Example test_destruct_singleton_under_definition P :
      simple_rep P -∗ P.
    Proof.
      iIntros "H".
      iNamed "H".
      Fail iExact "HP".
    Abort.

    Example test_nested_destruct Ψ :
      ⊢ ("%wf" ∷ ⌜True⌝ ∗
      "*" ∷ ∃ y, "psi" ∷ Ψ y) -∗
      ∃ x, Ψ x.
    Proof.
      iNamed 1.
      iExists y; iExact "psi".
    Qed.

    Example test_nested_destruct_conjuncts Ψ :
      ("%wf" ∷ ⌜True⌝ ∗
      "*" ∷ ∃ y, "psi" ∷ Ψ y ∗ "psi2" ∷ Ψ (2+y)) -∗
      ∃ x, Ψ x.
    Proof.
      iNamed 1.
      iExists (2+y); iExact "psi2".
    Qed.

    Example test_nested_destruct_middle P Ψ :
      ("HP1" ∷ P ∗
       "*" ∷ (∃ y, "psi" ∷ Ψ y ∗ "psi2" ∷ Ψ (2+y)) ∗
       "HP2" ∷ P) -∗
      ∃ x, Ψ x ∗ P.
    Proof.
      iNamed 1.
      iExists (2+y); iFrame "psi2 HP2".
    Qed.

    Example test_frame_named_spatial P1 P2 :
      "H1" ∷ P1 ∗ "H2" ∷ P2 -∗
      "H1" ∷ P1 ∗ "H2" ∷ P2.
    Proof.
      iIntros "I". iNamed "I".
      iFrameNamed.
    Qed.

    Example test_frame_named_persistent P1 P2 :
      "#H1" ∷ □ P1 ∗ "H2" ∷ P2 -∗
      "#H1" ∷ □ P1 ∗ "H2" ∷ P2.
    Proof.
      iIntros "I".
      iNamed "I".
      iFrameNamed.
    Qed.

    Example test_frame_named_pure P1 P2 :
      "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ □ P1 ∗ "H2" ∷ P2 -∗
      "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ P1 ∗ "H2" ∷ P2.
    Proof.
      iIntros "I". iNamed "I".
      iFrameNamed.
    Qed.

    Lemma env_modus_ponens (Γ: envs PROP) (Q Q': PROP) :
      envs_entails Γ Q' →
      (Q' ⊢ Q) →
      envs_entails Γ Q.
    Proof. intros H <- => //. Qed.

    Example test_inamedaccu_serialize P1 P2 :
      P1 ∗
      P1 ∗ P2 ∗
      P2 ∗
      P1 ∗ P2 -∗
      P1 ∗ P1 ∗ P1 ∗ P2 ∗ P2 ∗ P2.
    Proof.
      iIntros "(H1&?&?&H2&?&?)".
      eapply env_modus_ponens.
      - iNamedAccu.
      - iNamed 1.
        (* should recover the same context (modulo renaming of anonymous
        hypotheses) *)
        iFrame.
    Qed.

  End tests.
End tests.
