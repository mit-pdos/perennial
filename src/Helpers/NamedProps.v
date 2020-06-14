From iris.proofmode Require Import tactics environments intro_patterns.
From iris_string_ident Require Import ltac2_string_ident.

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
  - [iNamed 1] on a wand introduces and destructs the the premise.
  - [iFrameNamed] is a work-in-progress tactic to frame a goal with named
    conjuncts with the hypotheses using the names. This is intended to be much
    faster than framing the entire persistent and spatial contexts.

  Note that this library provides general support for propositions and are not
  specific to definitions. You can use them in Hoare logic preconditions (to
  make the first iIntros more stable), in the postcondition (to make it easier
  for the caller to re-introduce hypotheses), or in loop invariants (to serve
  both of these purposes).
 *)

Section named.
  Context {PROP:bi}.

  Definition named (name: string) (P: PROP): PROP := P.

  Theorem to_named name P : P -∗ named name P.
  Proof. auto. Qed.
  Theorem from_named name P : named name P -∗ P.
  Proof. auto. Qed.

  Fixpoint env_to_named_prop_go (acc : PROP) (Γ : env PROP) : PROP :=
    match Γ with
    | Enil => acc
    | Esnoc Γ (INamed name) P => env_to_named_prop_go (named name P ∗ acc)%I Γ
    | Esnoc Γ _ P => env_to_named_prop_go (P ∗ acc)%I Γ
    end.
  Definition env_to_named_prop (Γ : env PROP) : PROP :=
    match Γ with
    | Enil => emp%I
    | Esnoc Γ (INamed name) P => env_to_named_prop_go (named name P) Γ
    | Esnoc Γ _ P => env_to_named_prop_go P Γ
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

Ltac string_to_ident s :=
  let ident_fun := constr:(ltac:(ltac_tactics.string_to_ident_hook s)) in
  lazymatch ident_fun with
  | λ (x:_), _ => x
  end.

Local Ltac iDeex_go i x H :=
  let x' := fresh x in
  iDestructHyp i as (x') H.

(* iDeexHyp is like [iDestruct "H" as (?) "H"] except that it preserves the name
of the binder and repeats while the goal is an existential *)
Ltac iDeexHyp H :=
  let i := to_pm_ident H in
  let rec go _ := lazymatch goal with
                  (* check this separately because red on bi_exist produces an unseal *)
                  | |- context[Esnoc _ i (bi_exist (fun x => _))] =>
                    first [ iDeex_go i x H | fail "iDeexHyp: could not deex" H ]
                  | |- context[Esnoc _ i ?P] =>
                    let P := (eval red in P) in
                    lazymatch P with
                    | bi_exist (fun x => _) =>
                      first [ iDeex_go i x H | fail "iDeexHyp: could not deex" H ]
                    | _ => fail "iDeexHyp:" H "is not an ∃"
                    end
                  end in
  go tt; repeat go tt.

Ltac iDeex :=
  repeat match goal with
         | |- context[Esnoc _ ?i (bi_exist (fun x => _))] =>
           iDeex_go
         end.

Local Ltac iNameHyp_go H :=
  let i := to_pm_ident H in
  lazymatch goal with
  | |- context[Esnoc _ i (named ?name ?P)] =>
    let Htmp := iFresh in
    iRename i into Htmp;
    (* we treat a couple patterns specially: *)
    let pat := intro_pat.parse_one name in
    lazymatch pat with
    (* pure intros are freshened (otherwise they block using iNamed) *)
    | IPure (IGallinaNamed ?name) =>
      let id := string_to_ident name in
      let id := fresh id in
      iPure Htmp as id
    (* the token "*" causes iNamed to recurse *)
    | IForall => iNamed_go Htmp
    | _ => iDestruct (from_named with Htmp) as pat
    end;
    (* TODO: we do this renaming so we can clear the original hypothesis, but
    this only happens when it isn't consumed (when P is persistent); ideally we
    would do this whole manipulation with something lower-level that always
    replaced the hypothesis, but also supported an intro pattern for the result.
    Otherwise this may have significant performance cost with large
    environments. *)
    try iClear Htmp
  | |- context[Esnoc _ i _] =>
    fail "iNameHyp: hypothesis" H "is not a named"
  | _ => fail 1 "iNameHyp: hypothesis" H "not found"
  end with
  (* The core of iNamed is destructing and recursing over the resulting
   conjuncts; the implementation currently just calls iDestruct and then
   attempts to name the new anonymous hypotheses, but a better implementation
   would probably use the IntoSep typeclass and look for names right then. We
   might also want a dedicated typeclass that can provide names, in case they
   need to come from elsewhere (the main test case for this is PropRestore). *)
  (* Ltac *) iNamedDestruct H :=
  let rec go H :=
      first [iNameHyp_go H
            | let Htmp1 := iFresh in
              let Htmp2 := iFresh in
              let pat := constr:(IList [[IIdent Htmp1; IIdent Htmp2]]) in
              iDestruct H as pat;
              iNameHyp_go Htmp1; go Htmp2
            | idtac ]
  in go H with
  (* this is the top-level iNamed H tactic. *)
  (* Ltac *) iNamed_go H :=
  lazymatch H with
  | 1%Z => let i := iFresh in iIntros i; iNamed_go i
  | 1%nat => let i := iFresh in iIntros i; iNamed_go i
  | _ => (* first destruct the existentials, then split the conjuncts (but only
    these two levels, since the user might destruct only a few levels deep) *)
    try iDeexHyp H;
    iNamedDestruct H
  end.

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
  iStartProof; eapply tac_named_accu; [
    first [ cbv [ env_to_named_prop env_to_named_prop_go ];
            reduction.pm_reflexivity | fail 1 "iNamedAccu: not an evar" ]
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

(* TODO: maybe we should move tests out *)
Module tests.
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

    Example test_nested_destruct Ψ :
      ⊢ ("%wf" ∷ ⌜True⌝ ∗
      "*" ∷ ∃ x, "psi" ∷ Ψ x) -∗
      ∃ x, Ψ x.
    Proof.
      iIntros "H"; iNamed "H".
      iExists _; iExact "psi".
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
      iIntros "I". iNamed "I".
      iFrameNamed.
    Qed.

    Example test_frame_named_pure P1 P2 :
      "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ □ P1 ∗ "H2" ∷ P2 -∗
      "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ P1 ∗ "H2" ∷ P2.
    Proof.
      iIntros "I". iNamed "I".
      iFrameNamed.
    Qed.

  End tests.
End tests.
