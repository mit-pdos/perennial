(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.prelude Require Export prelude.
From Perennial.program_logic Require Import language ectx_language.
From iris.prelude Require Import options.

(** TAKE CARE: When you define an [ectxiLanguage] canonical structure for your
language, you need to also define a corresponding [language] and [ectxLanguage]
canonical structure for canonical structure inference to work properly. You
should use the coercion [EctxLanguageOfEctxi] and [LanguageOfEctx] for that, and
not [ectxi_lang] and [ectxi_lang_ectx], otherwise the canonical projections will
not point to the right terms.

A full concrete example of setting up your language can be found in [heap_lang].
Below you can find the relevant parts:

  Module heap_lang.
    (* Your language definition *)

    Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
    Proof. (* ... *) Qed.
  End heap_lang.

  Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
  Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
  Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.
*)

Section ectxi_language_mixin.
  Context {expr val ectx_item state global_state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 g1 κ e2 σ2 g2 efs : head_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None;

    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
    (** [fill_item] is always injective on the expression for a fixed
        context. *)
    mixin_fill_item_val_inv Ki v v' :
      is_Some (to_val (fill_item Ki (of_val v))) → is_Some (to_val (fill_item Ki (of_val v')));
    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);
    (** [fill_item] with (potentially different) non-value expressions is
        injective on the context. *)
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    (** If [fill_item Ki e] takes a head step, then [e] is a value (unlike for
        [ectx_language], an empty context is impossible here).  In other words,
        if [e] is not a value then wrapping it in a context does not add new
        head redex positions. *)
    mixin_head_ctx_step_val Ki e σ1 g1 κ e2 σ2 g2 efs :
      head_step (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e);
  }.
End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;
  global_state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → global_state → list observation → expr → state → global_state → list expr → Prop;

  ectxi_language_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxiLanguage {_ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fill_item {_} _ _.
Global Arguments head_step {_} _ _ _ _ _ _.

Section ectxi_language.
  Context {Λ : ectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val_inv Ki v v' :
      is_Some (to_val (fill_item Ki (of_val v))) → is_Some (to_val (fill_item Ki (of_val v'))).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 g1 κ e2 σ2 g2 efs :
    head_step (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.

  Definition fill (K : ectx) (e : expr Λ) : expr Λ := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill head_step.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    assert (to_of_val: ∀ (v : val Λ), to_val (of_val v) = Some v).
    { apply ectxi_language_mixin. }
    assert (of_to_val : ∀ e (v : val Λ), to_val e = Some v → of_val v = e).
    { apply ectxi_language_mixin. }
    split.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - intros K; induction K as [|Ki K IH].
      * intros ??. rewrite ?to_of_val //=. eauto.
      * simpl. intros v v' Hval_full.
        assert (Hval': is_Some (to_val (fill_item Ki (of_val v')))).
        { by apply fill_val, (fill_item_val_inv Ki _ v') in Hval_full. }
        assert (Hval: is_Some (to_val (fill_item Ki (of_val v)))).
        { by apply fill_val in Hval_full. }
        destruct Hval as (v0&Heq).
        destruct Hval' as (v0'&Heq').
        apply of_to_val in Heq'.
        apply of_to_val in Heq.
        rewrite -Heq'.
        rewrite -Heq in Hval_full.
        eapply IH; eauto.
    - intros K K' e1 κ e1' σ1 g1 e2 σ2 g2 efs Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
    - intros K e1 σ1 g1 κ e2 σ2 g2 efs.
      destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros ?%head_ctx_step_val; eauto using fill_val.
  Qed.

  Canonical Structure ectxi_lang_ectx := EctxLanguage ectxi_lang_ectx_mixin.
  Canonical Structure ectxi_lang := LanguageOfEctx ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Instance ectxi_lang_ctx_item Ki : LanguageCtx (fill_item Ki).
  Proof. change (LanguageCtx (fill [Ki])). apply _. Qed.
End ectxi_language.

Global Arguments ectxi_lang_ectx : clear implicits.
Global Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang_ectx : ectxiLanguage >-> ectxLanguage.
Coercion ectxi_lang : ectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage :=
  let '@EctxiLanguage E V C St GSt K of_val to_val fill head mix := Λ in
  @EctxLanguage E V (list C) St GSt K of_val to_val _ _ _ _
    (@ectxi_lang_ectx_mixin (@EctxiLanguage E V C St GSt K of_val to_val fill head mix)).
