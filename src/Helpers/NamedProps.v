From iris.proofmode Require Import tactics environments reduction.
From iris.base_logic.lib Require Import iprop.

From iris_string_ident Require ltac2_string_ident.

Section named.
  Context {PROP:bi}.

  Definition named_def (name: string) (P: PROP): PROP := P.
  Definition named_aux : seal (@named_def). by eexists. Qed.
  Definition named := (@named_aux).(unseal).
  Definition named_eq : @named = @named_def := (@named_aux).(seal_eq).

  Theorem to_named name P : P -∗ named name P.
  Proof.
    rewrite named_eq /named_def.
    auto.
  Qed.

  Theorem from_named name P : named name P -∗ P.
  Proof.
    rewrite named_eq /named_def.
    auto.
  Qed.

  Lemma tac_named_and_destruct Δ i p j1 j2 (P P1 P2 Q: PROP) :
    envs_lookup i Δ = Some (p, P) →
    (if p
     then IntoAnd true P (named j1 P1) P2
     else IntoSep P (named j1 P1) P2) →
    match envs_simple_replace i p (Esnoc (Esnoc Enil (INamed j1) P1) j2 P2) Δ with
    | None => False
    | Some Δ' => envs_entails Δ' Q
    end →
    envs_entails Δ Q.
  Proof.
    rewrite named_eq /named_def.
    eapply coq_tactics.tac_and_destruct; eauto.
  Qed.
End named.

Ltac name_hyp H :=
  let i := lazymatch type of H with
           | string => constr:(INamed H)
           | ident => constr:(H)
           end in
  lazymatch goal with
  | |- context[Esnoc _ i (named ?name ?P)] =>
    iDestruct (from_named with i) as name
  | |- context[Esnoc _ i _] =>
    fail "name_hyp: hypothesis" H "is not a named"
  | _ => fail "name_hyp: hypothesis" H "not found"
  end.

Ltac name_named :=
  repeat match goal with
         | |- context[Esnoc _ ?i (named ?name ?P)] =>
           iDestruct (from_named with i) as name
         end.

Local Tactic Notation "iNamedDestruct_one" constr(H) "as" constr(H2) :=
  eapply tac_named_and_destruct with H _ _ H2 _ _ _; (* (i:=H) (j2:=H2) *)
  [pm_reflexivity ||
                  let H := pretty_ident H in
                  fail "iNamedDestruct:" H "not found"
  |pm_reduce; iSolveTC ||
                        let P :=
                            lazymatch goal with
                            | |- IntoSep ?P _ _ => P
                            | |- IntoAnd _ ?P _ _ => P
                            end in
                        fail "iAndDestruct: cannot destruct" P
  |pm_reduce].

(* this works and is probably faster but it doesn't treat the names as patterns
but just names *)
Ltac iNamedDestruct' H :=
  let Htmp := iFresh in
  iNamedDestruct_one "H" as Htmp;
  repeat (iNamedDestruct_one Htmp as Htmp);
  name_hyp Htmp.

(* this is a super-simple but maybe non-performant implementation *)
Ltac iNamedDestruct H :=
  let rec go H :=
      first [name_hyp H
            | let Htmp1 := iFresh in
              let Htmp2 := iFresh in
              let pat := constr:(intro_patterns.IList
                                   [[intro_patterns.IIdent Htmp1;
                                     intro_patterns.IIdent Htmp2]]) in
              iDestruct H as pat;
              name_hyp Htmp1; go Htmp2 ]
  in go H.

Ltac prove_named :=
  repeat rewrite -to_named.

(* TODO: maybe we should move tests out *)
Module tests.
  Section tests.
    Context {Σ:gFunctors}.
    Implicit Types (P Q R : iProp Σ).

    Example test_name_named_1 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q.
    Proof.
      iIntros "? ?".
      name_named.
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
    Qed.

    Example test_name_named_2 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q%I.
    Proof.
      iIntros "H₁ H₂".
      name_hyp "H₁".
      name_hyp "H₂".
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
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

    Example test_destruct_named_iNamedDestruct' P Q :
      ⊢ named "H1" P ∗
        named "H2" Q ∗
        named "H3" P ∗
        named "H4" Q
        -∗
        P ∗ Q ∗ P ∗ Q.
    Proof.
      iIntros "H".
      iNamedDestruct' "H".
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

    Example test_prove_named P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      (* TODO: can this work with an appropriate framing instance? *)
      Fail iFrame "HP".
    Abort.

    Example test_remove_named_in_goal P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      prove_named.
      iFrame.
    Qed.

  End tests.
End tests.
