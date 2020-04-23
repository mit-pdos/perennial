From iris.proofmode Require Import tactics environments.
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

  Global Instance frame_named : Frame p P (named name P) emp.
  Proof.
    rewrite named_eq /named_def.
    apply _.
  Qed.
End named.

Ltac to_pm_ident H :=
  lazymatch type of H with
  | string => constr:(INamed H)
  | ident => constr:(H)
  end.

Ltac name_hyp H :=
  let i := to_pm_ident H in
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
              name_hyp Htmp1; go Htmp2
            | idtac ]
  in go H.

Ltac iDeexHyp H :=
  let i := to_pm_ident H in
  let rec go _ := match goal with
                  | |- context[Esnoc _ i (bi_exist (fun x => _))] =>
                    iDestructHyp i as (x) H
                  end in
  go tt; repeat go tt.

Ltac iDeex :=
  repeat match goal with
         | |- context[Esnoc _ ?i (bi_exist (fun x => _))] =>
           iDestructHyp i as (x) i
         end.

Ltac iNamed H :=
  try iDeexHyp H;
  iNamedDestruct H.

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
      iFrame "HQ HP".
    Qed.

    Example test_remove_named_in_goal P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      prove_named.
      iFrame.
    Qed.

    Example test_exist_destruct (P: nat -> iProp Σ) Q :
      ⊢ (∃ x, named "HP" (P x) ∗ named "HQ" Q) -∗ (∃ x, P x) ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      iSplitL "HP"; [ iExists x | ]; iFrame.
    Qed.

    Example test_exist_destruct_no_naming (P: nat -> iProp Σ) Q :
      ⊢ (∃ x, P x) -∗ (∃ x, P x).
    Proof.
      iIntros "H".
      iNamed "H".
      iExists x; iFrame "H".
    Qed.

    Example test_iNamed_destruct_pat (foo: Prop) P Q :
      ⊢ named "[%Hfoo HP]" (⌜foo⌝ ∗ P) ∗
        named "HQ" Q ∗
        named "HP2" P
        -∗
        ⌜foo⌝ ∗ P ∗ Q ∗ P.
    Proof.
      iIntros "H".
      iNamed "H".
      iFrame "HP HQ HP2".
      iPureIntro; exact Hfoo.
    Qed.

  End tests.
End tests.
