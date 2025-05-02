From New.proof Require Import proof_prelude.
From iris.algebra.lib Require Import mono_list mono_nat dfrac_agree gmap_view.
From Coq Require Import Logic.ClassicalEpsilon.

Module cmra_expr.
Inductive t :=
| prod (A B : t)
| gmap (K : Type) `{Countable K} (V : t)
| mono_list (E : Type)
| frac
| dfrac
| agree (A : Type)
| excl (A : Type)
| gmap_view (K : Type) `{Countable K} (V : t)
.

Fixpoint interpret (x : t) : cmra :=
  match x with
  | prod A B => prodR (interpret A) (interpret B)
  | gmap K V => gmapR K (interpret V)
  | mono_list A => mono_listR (leibnizO A)
  | frac => fracR
  | dfrac => dfracR
  | agree A => agreeR (leibnizO A)
  | excl A => exclR (leibnizO A)
  | gmap_view K V => gmap_viewR K (interpret V)
  end.
End cmra_expr.

(* This would require ucmra for everything, which would exclude exclR. *)
(* Definition any_cmra : Type := discrete_funUR cmra_expr.interpret. *)

Inductive csigT {A : Type} P :=
| CexistT : ∀ (x : A), P x → csigT P
| Cinvalid : csigT P.
Arguments CexistT {_ _} (_).
Arguments Cinvalid {_ _}.

Definition any_cmra : Type := csigT cmra_expr.interpret.

Inductive any_cmra_equiv_instance : Equiv any_cmra :=
| CexistT_equiv {A} a b : a ≡ b → (CexistT A a) ≡ (CexistT A b)
| Cinvalid_equiv : Cinvalid ≡ Cinvalid.
Local Existing Instance any_cmra_equiv_instance.

Inductive any_cmra_dist_instance : Dist any_cmra :=
| CexistT_dist {A} a b i : a ≡{i}≡ b → (CexistT A a) ≡{i}≡ (CexistT A b)
| Cinvalid_dist i : Cinvalid ≡{i}≡ Cinvalid.
Local Existing Instance any_cmra_dist_instance.

Local Instance any_cmra_valid_instance : Valid any_cmra :=
  λ x, match x with CexistT A a => ✓ a | _ => False end.

Local Instance any_cmra_validN_instance : ValidN any_cmra :=
  λ n x, match x with CexistT A a => ✓{n} a | _ => False end.

Local Instance any_cmra_pcore_instance : PCore any_cmra :=
  λ x, match x with CexistT A a => CexistT A <$> pcore a | _ => Some Cinvalid end.

Local Instance any_cmra_op_instance : Op any_cmra :=
  λ x y,
    match x, y with
    | CexistT A a, CexistT A' a' =>
        match (excluded_middle_informative (A = A')) with
        | right _ => Cinvalid
        | left eq_proof =>
            CexistT A' ((eq_rect A cmra_expr.interpret a A' eq_proof) ⋅ a')
        end
    | _, _ => Cinvalid
    end.

Definition any_cmra_ofe_mixin : OfeMixin any_cmra.
Proof. Admitted.

Lemma any_cmra_cmra_mixin : CmraMixin any_cmra.
Proof.
  split.
  - intros [] ? ? ? H.
    + inversion H; subst; rewrite /op /any_cmra_op_instance ///=.
      destruct excluded_middle_informative; constructor. rewrite H0 //.
    + cbn. constructor.
  -
Admitted.

Canonical Structure any_cmraO : ofe := Ofe any_cmra any_cmra_ofe_mixin.
Canonical Structure any_cmraR := Cmra any_cmra any_cmra_cmra_mixin.

Definition to_any (A : cmra_expr.t) a : any_cmra :=
  CexistT A a.

Lemma any_cmra_validN_op A B a b n :
  ✓{n} (CexistT A a ⋅ CexistT B b) ↔
  ∃ (pf : A = B), ✓{n}((eq_rect A _ a B pf) ⋅ b).
Proof.
Admitted.

Lemma any_cmra_validN_op_invalid_r A a n :
  ✓{n} (CexistT A a ⋅ Cinvalid) → False.
Proof.
Admitted.

Lemma any_cmra_validN_op_invalid_l A a n :
  ✓{n} (Cinvalid ⋅ CexistT A a) → False.
Proof.
Admitted.

Lemma any_cmra_validN A a n :
  ✓{n} CexistT A a ↔ ✓{n} a.
Proof. done. Qed.

Lemma any_cmra_valid A a :
  ✓ CexistT A a ↔ ✓ a.
Proof. done. Qed.

Lemma any_cmra_update {A : cmra_expr.t} a b :
  a ~~> b →
  to_any A a ~~> to_any A b.
Proof.
  unfold to_any. intros Hupd n [[]|] Hvalid.
  - rewrite any_cmra_validN_op in Hvalid. destruct Hvalid as [-> Hvalid].
    simpl. rewrite any_cmra_validN_op. eexists eq_refl.
    simpl in *. specialize (Hupd n (Some c)). by apply Hupd.
  - simpl in *. by apply any_cmra_validN_op_invalid_r in Hvalid.
  - simpl in *. rewrite !any_cmra_validN in Hvalid |- *.
    specialize (Hupd n None). by apply Hupd.
Qed.

Section own.
Context `{!inG Σ any_cmraR}.

Class SimpleCmra A :=
  {
    Aexp : cmra_expr.t;
    eq_proof : A = cmra_expr.interpret Aexp;
  }.

Definition own_any {A : cmra} γ (a : A) : iProp Σ :=
  ∃ (_ : SimpleCmra A), own γ (CexistT Aexp (eq_rect A id a _ eq_proof) : any_cmra).

Lemma own_any_update γ {A : cmra} (a a' : A) :
  a ~~> a' →
  own_any γ a ==∗ own_any γ a'.
Proof.
  intros Hupd. iIntros "[% Hown]".
  iExists _. iApply (own_update with "Hown").
  apply any_cmra_update. simpl. destruct H.
  simpl in *. destruct eq_proof0. simpl.
  apply Hupd.
Qed.

Lemma own_any_alloc `{!SimpleCmra A} (a : A) :
  ✓ a →
  ⊢ |==> ∃ γ, own_any γ a.
Proof.
  intros Hvalid.
  iMod (own_alloc (CexistT Aexp (eq_rect A id a _ eq_proof) : any_cmra)) as (γ) "H".
  { rewrite any_cmra_valid. simpl. destruct SimpleCmra0.
    simpl in *. destruct eq_proof0. simpl in *. done. }
  by iFrame.
Qed.

Instance mlist_simple_cmra (A : Type) : SimpleCmra (mono_listR (leibnizO A)).
Proof. by eexists (cmra_expr.mono_list A). Qed.

Lemma own_any_mono_list (l : list nat) :
  ⊢ |==> ∃ γ, own_any γ (●ML l).
Proof.
  iApply own_any_alloc. apply mono_list_auth_valid.
Qed.
End own.
