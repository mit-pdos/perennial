Local Lemma abstract_away_helper {A} (P: A -> Prop) (x y:A) :
  P y -> y = x -> P x.
Proof.
  intros; subst; auto.
Qed.

Ltac abstract_term t :=
  match goal with
  | |- ?g => let p := eval pattern t in g in
               match p with
               | ?P ?x => eapply (abstract_away_helper P)
               end
  end.
