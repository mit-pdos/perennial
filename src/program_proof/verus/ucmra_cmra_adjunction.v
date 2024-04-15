From Perennial.program_proof Require Import grove_prelude.
Require Import Coq.Logic.FunctionalExtensionality.

Section proof.

(*
Context (A:cmra).

Inductive G : Type :=
| Elem : A → G
| Gunit : G
.

Local Instance G_valid_instance : Valid G := λ g,
  match g with Elem a => ✓ a | Gunit => True end.
Local Instance G_validN_instance : ValidN G := λ n g,
  match g with Elem a => ✓{n} a | Gunit => True end.
Print PCore.
Local Instance G_pcore_instance : PCore G := λ g,
  match g with
  | Elem a => match (pcore a) with Some a => Some (Elem a) | None => Some Gunit end
  | Gunit => Some Gunit end.

(* Local Arguments G_pcore_instance !_ /. *)
Local Instance G_op_instance : Op G :=
  λ g1 g2,
  match g1, g2 with
  | Elem a, Elem b => Elem (a ⋅ b)
  | Gunit, Elem b => Elem b
  | Elem a, Gunit => Elem a
  | Gunit, Gunit => Gunit
  end
.

Local Instance G_dist_instance : Dist G :=
  λ n g1 g2,
  match g1, g2 with
  | Elem a, Elem b => dist n a b
  | Gunit, Elem b => False
  | Elem a, Gunit => False
  | Gunit, Gunit => True
  end
.

Local Instance G_equiv_instance : Equiv G :=
  λ g1 g2,
  match g1, g2 with
  | Elem a, Elem b => a ≡ b
  | Gunit, Elem b => False
  | Elem a, Gunit => False
  | Gunit, Gunit => True
  end
.

  Lemma option_cmra_mixin : CmraMixin (option A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros [a|] n; destruct 1; constructor; ofe_subst.
    - destruct 1. { ofe_subst.
    - by destruct 1; rewrite /validN /option_validN_instance //=; ofe_subst.

Lemma G_cmra_mixin : CmraMixin G.
Proof.
  apply cmra_total_mixin.
  - rewrite /pcore /G_pcore_instance /=. destruct x; try done.
    destruct (pcore c); done.
  - intros [a|] n.
    { intros [|] [|] Heq; rewrite /op /dist //= in Heq |- *; try done.
      by setoid_rewrite Heq. }
    { intros [|] [|] Heq; rewrite /op /dist //= in Heq |- *; done. }
  - intros n x y Heq.
    {
      rewrite /dist /G_dist_instance //= in Heq |-.
      setoid_rewrite Heq.
      rewrite /core /pcore /=.
      destruct (pcore c), (pcore c0).
      { simpl.
    }
 *)

  Definition UcmraMorphism {A B : ucmra} (f : A → B) : Prop :=
    CmraMorphism f ∧ f ε ≡ ε.

  Definition G_obj : ucmra → cmra := ucmra_cmraR.
  Definition G_arrow {A B:ucmra} : (A → B) → (ucmra_cmraR A → ucmra_cmraR B) :=
    λ f, f.

  Lemma G_arrow_functorial (A B:ucmra) (f: A → B):
    UcmraMorphism f → CmraMorphism (G_arrow f).
  Proof. by intros []. Qed.

  Definition F_obj : cmra → ucmra := optionUR.
  Definition F_arrow {A B:cmra} : (A → B) → (optionUR A → optionUR B) :=
    λ f mx, f <$> mx.

  Lemma F_arrow_functorial (A B:cmra) (f: A → B):
    CmraMorphism f → UcmraMorphism (F_arrow f).
  Proof.
    intros []. split; eauto.
    split.
    - destruct 1; by ofe_subst.
    - intros n [|]; rewrite /validN /cmra_validN /= /ucmra_validN /=; try done.
      by apply cmra_morphism_validN.
    - intros [|]; rewrite /F_arrow /=; try done. by rewrite cmra_morphism_pcore.
    - intros [|] [|]; rewrite /F_arrow /=; try rewrite //=.
      { rewrite -Some_op. by constructor. }
  Qed.

  (* This uses the counit-unit definition for adjoint functors, since it is
     convenient to prove the "algebraic" formulas. *)
  (* According to that definition, F is a left adjoing of G iff there exist:
      η : 1_{cmra} → G∘F
      ϵ : F∘G → 1_{ucmra}
     such that
      1_F = ϵF ∘ Fη
      1_G = Gϵ ∘ ηG.
   *)
  Definition η (X:cmra) : (X → G_obj $ F_obj X) := Some.
  Definition ϵ (Y:ucmra) : (F_obj $ G_obj Y → Y) :=
    λ y, match y with None => ε | Some y => y end.

  Lemma eqn_F (Y:cmra) :
    @id (F_obj Y) = (ϵ (F_obj Y) ∘ F_arrow (η Y)).
  Proof.
    apply functional_extensionality.
    intros y. rewrite /ϵ /η /G_arrow //=. by destruct y.
  Qed.

  Lemma eqn_G (X:ucmra) :
    @id (G_obj X) = (G_arrow (ϵ X) ∘ η (G_obj X)).
  Proof. done. Qed.

  (* This proof has now exhibited a left adjoint F for the forgetful functor
     G : ucmra → cmra. *)

End proof.
