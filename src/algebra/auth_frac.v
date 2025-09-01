From iris.algebra Require Import auth updates local_updates.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

(** XXX: TODO, upsteam, although this proof is a mess *)
Lemma auth_frac_update {A: ucmra} q (a b b': A) :
  (a,b) ~l~> (a,b') → ●{q} a ⋅ ◯ b ~~> ●{q} a ⋅ ◯ b'.
Proof.
  intros Hup; apply cmra_total_update.
  move=> n [[[? b0]|] bf1] [/= VL [a0 [Eq [[bf2 Ha] VL2]]]]; do 2 red; simpl in *.
  + split; auto.
    assert (✓{n} to_agree a0).
    { econstructor. }
    assert (✓{n} b0) as Hb0val.
    { eapply cmra_validN_includedN; last first.
      { econstructor. rewrite comm. by symmetry. }
      eauto. }
    apply to_agree_uninjN in Hb0val as (a1&Heqa1).
    assert (a ≡{n}≡ a0) as Heqa.
    {
      apply to_agree_injN. eapply agree_valid_includedN.
      - econstructor.
      - econstructor; by symmetry.
    }
    assert (a1 ≡{n}≡ a0) as Heqa1'.
    {
      apply to_agree_injN. eapply agree_valid_includedN.
      - econstructor.
      - econstructor. rewrite Heqa1 comm. by symmetry.
    }
    move: Ha; rewrite !left_id -assoc => Ha.
    destruct (Hup n (Some (bf1 ⋅ bf2))) as [ ? He ]; simpl.
    { by rewrite Heqa. }
    { simpl. by rewrite Heqa. }
    simpl in He.
    exists a0. rewrite -Heqa1 Heqa1'.
    eexists; split_and!; eauto.
    * intros ? Hin.
      inversion Hin; subst; eexists; split_and!; first econstructor; eauto.
    * intros ? Hin. inversion Hin as [ | ? ? ? Hin2]; subst.
      ** exists a0; split; auto. repeat econstructor.
      ** inversion Hin2.
    * rewrite -Heqa He. simpl.
      rewrite left_id assoc. econstructor; eauto.
  + split; [done|]. apply to_agree_injN in Eq.
    move: Ha; rewrite !left_id -assoc => Ha.
    destruct (Hup n (Some (bf1 ⋅ bf2))); [by rewrite Eq..|]. simpl in *.
    exists a. split; [done|]. split; [|done]. exists bf2.
    by rewrite left_id -assoc.
Qed.

Lemma auth_frac_update_alloc {A: ucmra} (dq: dfrac) (a b': A):
  (a, ε) ~l~> (a,b') → (●{dq} a ~~> ●{dq} a ⋅ ◯ b').
Proof. intros H. rewrite -{1}(right_id _ _ (●{dq} a)). by eapply auth_frac_update in H. Qed.

Lemma auth_frac_update_core_id {A: ucmra} dq (a b: A) `{!CoreId b} :
  b ≼ a → ●{dq} a ~~> ●{dq} a ⋅ ◯ b.
Proof.
  intros Hincl. apply: auth_frac_update_alloc.
  rewrite -(left_id ε _ b). apply: core_id_local_update. done.
Qed.
