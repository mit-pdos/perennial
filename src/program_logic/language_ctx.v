From Perennial.program_logic Require Export language.

Section ctx.
Context {Λ: language}.

Instance id_ctx : LanguageCtx (Λ := Λ) (fun x => x).
Proof. split; intuition eauto. Qed.

Instance comp_ctx K K':
  LanguageCtx (Λ := Λ) K →
  LanguageCtx (Λ := Λ) K' →
  LanguageCtx (Λ := Λ) (λ x, K' (K x)).
Proof.
  intros Hctx Hctx'.
  split; intros.
  - by do 2 apply fill_not_val.
  - by do 2 apply fill_step.
  - edestruct (@fill_step_inv _ _ Hctx' (K e1')); eauto; intuition.
    { apply fill_not_val; auto. }
    subst.
    edestruct (@fill_step_inv _ _ Hctx); eauto; intuition.
    subst.
    eauto.
Qed.

End ctx.
