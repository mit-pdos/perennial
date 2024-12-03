From stdpp Require Import finite strings.

Lemma list_finite_lt_length `{Finite A} n : Finite { l : list A | length l < n }.
Proof.
  induction n as [| n IH].
  - exists [].
    * econstructor.
    * intros [x Hlt]. lia.
  - unshelve (refine (surjective_finite (λ v : {l : list A | length l < n} + {l : list A | length l = n},
                            match v with
                            | inl l => _
                            | inr r => _
                            end))).
    { refine (proj1_sig l ↾ _). abstract (destruct l; simpl; lia). }
    { refine (proj1_sig r ↾ _). abstract (destruct r; simpl; lia). }
    * intros [l Hleq].
      inversion Hleq.
      ** unshelve (eexists (inr (l ↾ _))); auto.
         simpl. apply sig_eq_pi; auto; apply _.
      ** unshelve (eexists (inl (l ↾ _))); auto.
         simpl. apply sig_eq_pi; auto; apply _.
Qed.

Lemma string_length_string_of_list_ascii l :
  String.length (String.string_of_list_ascii l) = length l.
Proof.
  induction l as [| a l IHl] => /=; auto.
Qed.

Lemma length_list_ascii_of_string s :
  length (String.list_ascii_of_string s) = String.length s.
Proof.
  induction s as [| a s IHl] => /=; auto.
Qed.

#[local]
Instance ascii_finite :
  finite.Finite Ascii.ascii.
Proof.
  eapply (enc_finite (Ascii.nat_of_ascii) (Ascii.ascii_of_nat) 256).
  - apply Ascii.ascii_nat_embedding.
  - apply Ascii.nat_ascii_bounded.
  - apply Ascii.nat_ascii_embedding.
Qed.

Lemma string_finite_Zlt_length (z : Z) :
  finite.Finite {k : string | (Z.of_nat (String.length k) < z)%Z }.
Proof.
  unshelve (refine (surjective_finite (λ v : {l : list Ascii.ascii | length l < Z.to_nat z},
                         (String.string_of_list_ascii (proj1_sig v) ↾ _)))).
  { abstract (rewrite string_length_string_of_list_ascii; destruct v; simpl; lia). }
  { apply list_finite_lt_length.  }
  intros [l Hlt].
  unshelve (eexists (String.list_ascii_of_string l ↾ _)).
  { abstract (simpl; rewrite length_list_ascii_of_string; lia). }
  simpl. apply sig_eq_pi; first (by apply _); simpl.
  rewrite String.string_of_list_ascii_of_string; auto.
Qed.
