From iris.proofmode Require Import coq_tactics reduction intro_patterns.
From Perennial.Helpers Require Export ipm.
From Perennial.iris_lib Require Import dfractional.
From Perennial.program_logic Require Export weakestpre.
Set Default Proof Using "Type".

Class UpdateIntoPersistently {M} (P Q : uPred M) :=
  update_into_persistently : P ⊢ |==> □ Q.
Arguments UpdateIntoPersistently {_} _%I _%I.
Arguments update_into_persistently {_} _%I _%I {_}.
#[global]
Hint Mode UpdateIntoPersistently + ! - : typeclass_instances.

#[global]
Instance UpdateIntoPersistently_Proper {M} :
  Proper ((≡) ==> (≡) ==> iff) (@UpdateIntoPersistently M).
Proof.
  intros P1 P2 Heq1 Q1 Q2 Heq2.
  rewrite /UpdateIntoPersistently.
  rewrite Heq1 Heq2 //.
Qed.

(* used when Q is an output (produced by going from P to Φ) *)
#[global]
Instance dfractional_update_into_persistently {M} (P: uPred M) (Φ: dfrac → uPred M) dq :
  AsDFractional P Φ dq →
  UpdateIntoPersistently P (Φ DfracDiscarded).
Proof.
  intros [-> ?].
  rewrite /UpdateIntoPersistently.
  iIntros "H".
  pose proof (dfractional_persistent Φ).
  iMod (dfractional_persist with "H") as "#H".
  iFrame "H". done.
Qed.

(* used when Q is a fixed input *)
#[global]
Instance dfractional_update_into_persistently' {M} (P Q: uPred M) (Φ: dfrac → uPred M) dq :
  AsDFractional P Φ dq →
  AsDFractional Q Φ (DfracDiscarded) →
  UpdateIntoPersistently P Q.
Proof.
  intros [-> ?] [-> ?].
  eapply dfractional_update_into_persistently; eauto.
Qed.

Lemma tac_update_into_persistently {M} (Δ: envs (uPred M)) i j p P P' Q Q' :
  envs_lookup i Δ = Some (p, P) →
  UpdateIntoPersistently P P' →
  ElimModal True p false (|==> □ P') (□ P') Q Q' →
  match envs_replace i p true (Esnoc Enil j P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q'
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_unseal=> Hget HPP' Hmodal HQ. rewrite envs_replace_singleton_sound //=.
  rewrite HPP' HQ.
  iIntros "[HP HQ]".
  iApply elim_modal; [ eassumption | done | ].
  iFrame "HP HQ".
Qed.

Tactic Notation "iPersist_hyp" constr(H) constr(H') :=
  eapply tac_update_into_persistently with H H' _ _ _ _;
  [ reduction.pm_reflexivity || fail "iPersist:" H "not  found"
  | tc_solve ||
    lazymatch goal with
    | |- UpdateIntoPersistently ?P _ =>
      fail "iPersist: could not turn" P "into something persistent"
    end
  | tc_solve ||
    fail "iPersist: could not eliminate update modality"
  | reduction.pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iPersist:" H' "not fresh"
     | _ => reduction.pm_prettify (* subgoal *)
     end
  ].

Ltac iPersist_one H := iPersist_hyp H H.

Ltac iPersist_list Hlist :=
  let Hs := (eval cbv in (String.words Hlist)) in
  let rec go xs :=
    match xs with
    | cons ?H ?xs' => iPersist_hyp H H; go xs'
    | nil => idtac
    end in
  go Hs.

Tactic Notation "iPersist" constr(H) := iPersist_list H.
Tactic Notation "iPersist" constr(H) "as" constr(ipat) :=
  let Htmp := iFresh in
  iPersist_hyp H Htmp; iDestruct Htmp as ipat.
