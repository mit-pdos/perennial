From stdpp Require Import gmap.
From iris.algebra Require Import agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export own saved_prop.
From iris.prelude Require Import options.
Import uPred.

(* Saved specs. *)
Notation savedSpecO Σ In Out := (In -d> (Out -d> iPropO Σ) -n> iPropO Σ).
Notation savedSpecG Σ In Out := (savedAnythingG Σ (In -d> (Out -d> ▶ ∙) -n> ▶ ∙)).
Notation savedSpecΣ In Out := (savedAnythingΣ (In -d> (Out -d> ▶ ∙) -n> ▶ ∙)).

Program Definition saved_spec_own {In Out : Type} `{!savedSpecG Σ In Out} (γ : gname)
    (Spec : savedSpecO Σ In Out)
  :=
  saved_anything_own (F := In -d> (Out -d> ▶ ∙) -n> ▶ ∙) γ
    (λ in_, (λne Φ : Out -d> laterO (iPropO Σ), Next (Spec in_ (λ out, later_car (Φ out))))).
Next Obligation.
  intros ????? Spec ?? Φ1 Φ2 HΦ.
  apply Next_contractive.
  destruct n; first done. simpl.
  eapply ofe_mor_ne.
  intros out.
  eapply (later_car_anti_contractive (S n)).
  eapply (HΦ out).
Qed.

Global Instance saved_spec_own_contractive {In Out : Type} `{!savedSpecG Σ In Out} γ :
  Contractive (saved_spec_own γ : savedSpecO Σ In Out → iPropO Σ).
Proof.
  solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | by auto | f_contractive | f_equiv ]).
Qed.

Section lemmas.
Context  {In Out : Type} `{!savedSpecG Σ In Out}.
Implicit Type Spec : savedSpecO Σ In Out.

Lemma saved_spec_alloc_strong (I : gname → Prop) Spec :
  pred_infinite I →
  ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_spec_own γ Spec.
Proof. iIntros (?). rewrite /saved_spec_own. by iApply saved_anything_alloc_strong. Qed.

Lemma saved_spec_alloc_cofinite (G : gset gname) Spec :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_spec_own γ Spec.
Proof. rewrite /saved_spec_own. iApply saved_anything_alloc_cofinite. Qed.

Lemma saved_spec_alloc Spec :
  ⊢ |==> ∃ γ, saved_spec_own γ Spec.
Proof. rewrite /saved_spec_own. iApply saved_anything_alloc. Qed.

(* We put the `x` on the outside to make this lemma easier to apply. *)
Lemma saved_spec_agree γ Spec1 Spec2 x Φ :
  saved_spec_own γ Spec1 -∗ saved_spec_own γ Spec2 -∗ ▷ (Spec1 x Φ ≡ Spec2 x Φ).
Proof.
  unfold saved_spec_own. iIntros "HΦ HΨ /=". iApply later_equivI.
  iDestruct (saved_anything_agree (F := In -d> (Out -d> ▶ ∙) -n> ▶ ∙) with "HΦ HΨ") as "Heq".
  rewrite discrete_fun_equivI.
  iSpecialize ("Heq" $! x).
  rewrite ofe_morO_equivI.
  iSpecialize ("Heq" $! (Next ∘ Φ)). simpl. done.
Qed.

End lemmas.
