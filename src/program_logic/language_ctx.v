From Perennial.program_logic Require Export language.

Section ctx.
Context {Λ: language}.

Instance id_ctx : LanguageCtx (Λ := Λ) (fun x => x).
Proof.
  split; intuition eauto.
  rewrite to_of_val; eauto.
Qed.

Instance comp_ctx K K':
  LanguageCtx (Λ := Λ) K →
  LanguageCtx (Λ := Λ) K' →
  LanguageCtx (Λ := Λ) (λ x, K' (K x)).
Proof.
  intros Hctx Hctx'.
  split; intros.
  - by do 2 apply fill_not_val.
  - destruct (to_val (K (of_val v))) as [Kv|] eqn:Heq; last first.
    { apply (@fill_not_val _ K' _ _) in Heq.
      eapply eq_None_not_Some in Heq; intuition. }
    assert (is_Some (to_val (K (of_val v')))) as Hsome'.
    { eapply fill_val_inv; eauto. }
    destruct Hsome' as (Kv'&Heq').
    apply of_to_val in Heq.
    match goal with
    | [ H: context[ K (of_val v)] |- _ ] => rewrite -Heq in H
    end.
    apply of_to_val in Heq'.
    rewrite -Heq'.
    eapply fill_val_inv. eauto.
  - by do 2 apply fill_step.
  - edestruct (@fill_step_inv _ _ Hctx' (K e1')); eauto; intuition.
    { apply fill_not_val; auto. }
    subst.
    edestruct (@fill_step_inv _ _ Hctx); eauto; intuition.
    subst.
    eauto.
Qed.

End ctx.
