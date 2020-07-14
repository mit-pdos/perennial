From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

Set Default Proof Using "Type".

(* TODO: upstream this *)
Section big_op.
Context `{Monoid M o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).
Section gset.
  Context `{Countable A} `{Countable B}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma set_map_union_singleton (h: A → B) X x:
    set_map h ({[x]} ∪ X) = ({[h x]} ∪ (set_map h X) : gset B).
  Proof. set_solver. Qed.

  Lemma big_opS_fmap (h: A → B) X (g: B → M):
    (∀ x y, h x = h y → x = y) →
    ([^o set] x ∈ set_map h X, g x) ≡ ([^o set] x ∈ X, g (h x)).
  Proof.
    intros Hinj.
    induction X as [|x X ? IH] using set_ind_L => //=; [ by rewrite big_opS_eq | ].
    rewrite set_map_union_singleton.
    rewrite ?big_opS_union.
    - rewrite ?big_opS_singleton IH //.
    - set_solver.
    - cut ((h x) ∉ (set_map h X : gset _)); first by set_solver.
      intros (x'&Heq&Hin)%elem_of_map.
      apply Hinj in Heq. subst. auto.
  Qed.

  Lemma big_opS_list `{Countable A} (Φ: A → M) (l: list A) :
    NoDup l →
    big_opS o Φ (list_to_set l) ≡ big_opL o (λ _ x, Φ x) l.
  Proof.
    induction l as [|x l]; intros Hnodup.
    - simpl.
      rewrite big_opS_empty //.
    - inversion Hnodup; subst; clear Hnodup.
      rewrite /= big_opS_union; last first.
      { rewrite disjoint_singleton_l.
        rewrite elem_of_list_to_set //. }
      rewrite big_opS_singleton.
      f_equiv.
      apply IHl; auto.
  Qed.
  End gset.
End big_op.

Lemma big_sepS_list {PROP:bi} `{Countable A} (Φ: A → PROP) (l: list A) :
  NoDup l →
  big_opS bi_sep Φ (list_to_set l) ⊣⊢ big_opL bi_sep (λ _ x, Φ x) l.
Proof. apply big_opS_list. Qed.
