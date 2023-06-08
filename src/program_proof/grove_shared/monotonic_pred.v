From iris.bi Require Export bi derived_laws.
From iris.proofmode Require Import proofmode.
Import interface.bi derived_laws.bi.

Section monotonicity.

Context `{R:Type, PROP:bi}.
(* double-dual/continuation monad *)
Class MonotonicPred (P:(R → PROP) → PROP) :=
  {
    monotonic_fact: (∀ Φ Ψ, □(∀ r, Φ r -∗ Ψ r) -∗ P Φ -∗ P Ψ);
  }.

Global Instance monotonic_const  P : MonotonicPred (λ _, P)%I.
Proof. constructor. iIntros (??) "#? $". Qed.

(* like `return r` *)
Global Instance monotonic_return (r:R) : MonotonicPred (λ Φ, Φ r)%I.
Proof. constructor. iIntros (??) "#H". iApply "H". Qed.

Global Instance monotonic_forall {T:Type} (Q: T → (R → PROP) → PROP) :
  (∀ x, MonotonicPred (Q x)) →
  MonotonicPred (λ Φ, ∀ x, Q x Φ)%I.
Proof. constructor. iIntros (??) "#H HQ %". iApply (monotonic_fact with "[] [HQ]").
       { done. } iApply "HQ". Qed.

(* XXX: a term of the form (λ Φ, ∀ x, Φ x) might get simplified to (bi_forall),
   so we need this instance. *)
Global Instance monotonic_forall' :
  MonotonicPred (PROP.(bi_forall)).
Proof. constructor. iIntros (??) "#H HQ %a". iApply "H".
       by iApply bi.forall_elim. (* FIXME: why doesn't [iApply "HQ".] work? *)
Qed.

(* This requires that the predicate transformer Q be monotonic for ANY v, not
   just the existentially quantified v that satisfies some properties that Q
   might insist.
   E.g.
     ∃ (v:nat), ⌜v = 0⌝ ∗
          (⌜v == 0⌝ ∗ <monotonic in Φ>) ∨
          <not monotonic in Φ>
   is technically monotonic in Φ, but not syntactically so. This instance isn't
   designed to work with such a transformer.
 *)
Global Instance monotonic_exists {T:Type} (Q: T → (R → PROP) → PROP) :
  (∀ v, MonotonicPred (Q v)) →
  MonotonicPred (λ Φ, ∃ v, Q v Φ)%I.
Proof. constructor. iIntros (??) "#H (% & HQ)". iExists _.
       by iApply (monotonic_fact with "[] HQ").
Qed.

Global Instance monotonic_sep P Q :
  MonotonicPred P → MonotonicPred Q → MonotonicPred (λ Φ, P Φ ∗ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#?[HP ?]".
  iSplitL "HP".
  { clear H0. by iDestruct (monotonic_fact with "[] [-]") as "$". }
  { by iDestruct (monotonic_fact with "[] [-]") as "$". }
Qed.

Global Instance monotonic_conjunction P Q :
  MonotonicPred P → MonotonicPred Q → MonotonicPred (λ Φ, P Φ ∧ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#? HP".
  iSplit.
  { iDestruct "HP" as "[H _]". clear H0. by iDestruct (monotonic_fact with "[] [-]") as "$". }
  { iDestruct "HP" as "[_ H]". by iDestruct (monotonic_fact with "[] [-]") as "$". }
Qed.

Global Instance monotonic_disjunction P Q :
  MonotonicPred P → MonotonicPred Q → MonotonicPred (λ Φ, P Φ ∨ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#?[HP|HQ]".
  { clear H0. iLeft. by iDestruct (monotonic_fact with "[] [-]") as "$". }
  { iRight. by iDestruct (monotonic_fact with "[] [-]") as "$". }
Qed.

Global Instance monotonic_wand P Q :
  MonotonicPred Q → MonotonicPred (λ Φ, P -∗ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#Hwand HΦ HP".
  iSpecialize ("HΦ" with "HP").
  by iDestruct (monotonic_fact with "[] [-]") as "$".
Qed.

(* XXX: technically could have slightly weaker assumption specifically about P and Q *)
Global Instance monotonic_impl `{BiAffine PROP} P Q :
  MonotonicPred Q → MonotonicPred (λ Φ, P → Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "Hwand HΦ".
  iCombine "Hwand HΦ" as "HH".
  iDestruct (sep_and with "HH") as "HH".
  iApply (impl_intro_r); last iAccu.
  iIntros "HH".
  iDestruct ((assoc _ (Assoc:=bi.and_assoc)) with "HH") as "HH".
  iDestruct (persistent_and_affinely_sep_l with "HH") as "[Hwand HH]".
  iDestruct (affinely_elim with "Hwand") as "#Hwand2".
  iDestruct (impl_elim_l with "HH") as "HH".
  by iApply monotonic_fact.
Qed.

Global Instance monotonic_fupd `{BiFUpd PROP} Eo Ei Q :
  MonotonicPred Q → MonotonicPred (λ Φ, |={Eo,Ei}=> Q Φ)%I.
Proof.
  constructor. iIntros (??) "#? >HQ". iModIntro.
  by iApply monotonic_fact.
Qed.

Global Instance monotonic_intuitionistically P :
  MonotonicPred P → MonotonicPred (λ Φ, □ P Φ)%I.
Proof.
  constructor. iIntros (??) "#? #HP".
  iModIntro. by iApply monotonic_fact.
Qed.

End monotonicity.

Section monotonicity_examples.
Context `{PROP:bi}.
Context `{!BiAffine PROP}.
Context `{!BiFUpd PROP}.
Context {A B C : PROP}.

Local Example spec1 Φ : PROP := A ∗ B ∗ (C -∗ Φ 0).
Local Example spec2 Φ : PROP := |={⊤,∅}=> (A ∨ B) ∗ (B ={∅,⊤}=∗ Φ 0).

(* specs with quantifiers *)
Local Example qspec1 Φ : PROP := (∀ (x:nat), Φ x).
Local Example qspec2 Φ : PROP := |={⊤,∅}=> ∀ x, A ∗ (∃ v, ⌜v < x⌝ ∗ B ={∅,⊤}=∗ Φ (x + v)).

Local Definition monotonic_spec_1 : MonotonicPred spec1 := _.
Local Definition monotonic_spec_2 : MonotonicPred spec2 := _.

Local Definition monotonic_qspec_1 : MonotonicPred qspec1 := _.
Local Definition monotonic_qspec_2 : MonotonicPred qspec2 := _.
End monotonicity_examples.
