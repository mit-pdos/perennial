Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre.
From iris.algebra Require Import auth functions.

From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

Program Definition uPred_completable_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼{n'} x' → n' ≤ n → ✓{n'} x' → ∃ y, ✓{n'} (x' ⋅ y) ∧ P n' (x' ⋅ y) |}.
Next Obligation.
  intros M P n1 n2 x x' H Hle1 Hl2 n3 x'' Hle1' Hle2' Hval.
  edestruct (H n3 x'') as (y&?); eauto.
  - etransitivity; last eassumption.
    { eapply cmra_includedN_le; eauto. lia. }
  - lia.
Qed.
Definition uPred_completable_aux : seal (@uPred_completable_def). by eexists. Qed.
Definition uPred_completable {M} := uPred_completable_aux.(unseal) M.
Definition uPred_completable_eq :
  @uPred_completable = @uPred_completable_def := uPred_completable_aux.(seal_eq).

Global Instance complete_ne {M} n : Proper (dist n ==> dist n) (@uPred_completable M).
Proof.
  intros P Q Heq. rewrite uPred_completable_eq. split=> n' x ?? //=;
  split; intros HP n'' x'' ???;
  edestruct (HP n'' x'') as (y&?&?); eauto;
  exists y; split; auto; eapply Heq; eauto; lia.
Qed.

Notation "<comp> P" := (uPred_completable P) (at level 20, right associativity) : bi_scope.

Lemma auth_validN_3 {A: ucmraT} n (a: A) b : ✓{n} (● a ⋅ b) → ∃ a0, b = ◯ a0 ∧ a0 ≼{n} a ∧ ✓{n} a.
Proof.
  destruct b as [[b_auth|] b_own] => //=.
  intros. exists b_own. split; auto; eapply auth_validN_2; eauto.
Qed.

Lemma complete_mono {M} (P Q: uPred M) :
  (P -∗ Q) →
  <comp> P -∗ <comp> Q.
Proof.
  intros HPQ. rewrite uPred_completable_eq; split => n x Hval HP n' x' Hincl Hle Hv.
  edestruct (HP n' x') as (y&?&?); eauto.
  exists y; split; auto. eapply HPQ; eauto.
Qed.

Global Instance complete_mono' {M}:
  Proper ((⊢) ==> (⊢)) (@uPred_completable M).
Proof. intros P Q HPQ. by apply complete_mono. Qed.

Lemma complete_plainly_sep {M} (P Q: uPred M) :
  <comp> P ∗ ■ Q -∗ <comp> (P ∗ ■ Q).
Proof.
  unseal. rewrite uPred_completable_eq; split => n x Hval HP n' x' Hincl Hle Hv.
  destruct HP as (x1&x2&Heqx&HP&HQ).
  edestruct (HP n' x') as (y&?); eauto.
  { etransitivity; last eauto.
    exists x2. eapply dist_le; eauto.
  }
  exists y; intuition.
  exists (x' ⋅ y), (ε: M); rewrite right_id; split_and!; auto.
  rewrite /uPred_plainly_def//= in HQ *. red. red in HQ.
  eapply uPred_mono; try eassumption. reflexivity.
Qed.

Lemma complete_plainly_elim {M} (P: uPred M) :
  <comp> ■ P -∗ ■ P.
Proof.
  unseal. rewrite uPred_completable_eq. split => n x Hval HP.
  edestruct (HP n x) as (x'&?&?); auto.
Qed.

Lemma complete_plain_elim {M} (P: uPred M) `{!Plain P}:
  <comp> P -∗ P.
Proof. rewrite {1}(plain P) complete_plainly_elim plainly_elim //. Qed.

Lemma complete_intro {M} (P: uPred M) :
  P -∗ <comp> P.
Proof.
  rewrite uPred_completable_eq. split => n x Hval HP.
  intros n' x' ???. exists ε. rewrite ?right_id; intuition.
  eapply uPred_mono with (n2 := n') (x1 := x) (x2 := x) in HP; eauto.
  eapply uPred_mono; eauto.
Qed.

Section auth_complete.
Context `{Hin: inG Σ (authR A)}.

(* TODO: clean this up if it turns out to be what we need *)
Lemma complete_auth γ a:
  own γ (● a) -∗ <comp> own γ (● a ⋅ ◯ a).
Proof.
  rewrite own_eq uPred_completable_eq /own_def //=; unseal.
  split => n x Hv Hown n' x' Hincl1 Hle1 Hval1.
  eapply uPred_mono with (n2 := n') (x1 := x) (x2 := x) in Hown; eauto.
  eapply uPred_mono with (n2 := n') (x2 := x') in Hown; eauto.
  clear x Hincl1 Hv Hle1 n.
  inversion Hown as [y Heq].
  setoid_rewrite Heq.
  assert (Hvaly: ✓{n'} y).
  { rewrite Heq in Hval1 *. apply cmra_validN_op_r. }
  rewrite /iRes_singleton //=.
  set (ma0 := y Hin.(inG_id) !! γ).
  destruct ma0 as [a0'|] eqn:Heq_ma0.
  {
    set (y' := ofe_fun_insert Hin.(inG_id) ε y).
    set (a0 := cmra_transport (eq_sym inG_prf) a0').
    assert (Heq_split: y ≡{n'}≡ ofe_fun_singleton Hin.(inG_id) (y Hin.(inG_id)) ⋅ y').
    { intros i. rewrite /y'.
      destruct (decide (i = Hin.(inG_id))).
      - subst.
        rewrite ?ofe_fun_lookup_op ofe_fun_lookup_insert right_id.
        rewrite ?ofe_fun_lookup_singleton //=.
      - rewrite ?ofe_fun_lookup_op ofe_fun_lookup_insert_ne // ofe_fun_lookup_singleton_ne //
                left_id //.
    }
             assert (a0' = cmra_transport (Hin.(@inG_prf Σ (authR A))) a0) as Heq'.
             { rewrite /a0 //= /cmra_transport.
               rewrite rew_opp_r //=. }
    assert (✓{n'} (● a ⋅ a0)).
    { rewrite /a0.
      rewrite Heq in Hval1 * => Hval1.
      specialize (Hval1 Hin.(inG_id) γ).
      rewrite ofe_fun_lookup_op /iRes_singleton ofe_fun_lookup_singleton gmap.lookup_op
              ?lookup_singleton in Hval1 *.
      rewrite /ma0 in Heq_ma0. rewrite Heq_ma0 in Hval1.
      rewrite -Some_op Some_validN in Hval1 *.
      rewrite Heq' -cmra_transport_op cmra_transport_validN /cmra_transport rew_opp_r //=.
    }
    rewrite {1}Heq_split {1}assoc in Heq * => Heq.
    edestruct (auth_validN_3 n' a) as (b&Heq_b&Hincl&?); eauto.
    destruct Hincl as [b' Hincl].
    exists (iRes_singleton γ (◯ b')).
    split.
    * rewrite Heq_split. intros i.
      destruct (decide (i = Hin.(inG_id))) as [->|].
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton /y'
                 ofe_fun_lookup_insert right_id //=.
         intros γ'.
         destruct (decide (γ = γ')) as [->|].
         *** rewrite ?gmap.lookup_op ?lookup_singleton. rewrite /ma0 in Heq_ma0.
             rewrite Heq_ma0. rewrite -?Some_op Some_validN.
             rewrite Heq'.
             rewrite -?cmra_transport_op cmra_transport_validN Heq_b.
             rewrite -assoc -auth_frag_op -Hincl auth_validN_2; split; eauto.
         *** rewrite ?gmap.lookup_op ?lookup_singleton_ne //=.
             rewrite right_id left_id. eapply Hvaly.
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton_ne //=
                 ?left_id ?right_id //=.
         rewrite Heq in Hval1 * => Heq''.
         apply cmra_validN_op_r in Heq''; eauto.
    * red => //=. rewrite Heq_split.
      exists ((ofe_fun_singleton Hin.(inG_id) (delete γ (y Hin.(inG_id)))) ⋅ y').
      intros i.
      destruct (decide (i = Hin.(inG_id))) as [->|].
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton /y'
                 ofe_fun_lookup_insert right_id //=.
         intros γ'.
         destruct (decide (γ = γ')) as [->|].
         *** rewrite ?gmap.lookup_op ?lookup_singleton. rewrite /ma0 in Heq_ma0.
             rewrite Heq_ma0. rewrite -?Some_op.
             rewrite Heq'.
             rewrite -?cmra_transport_op Heq_b ?auth_frag_op ?lookup_delete.
             apply Some_ne, cmra_transport_ne. rewrite Hincl -?assoc //=.
         *** rewrite ?gmap.lookup_op ?lookup_singleton_ne ?lookup_delete_ne //=.
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton_ne //=
                 ?left_id ?right_id //=.
  }
  {
    assert (✓{n'} a).
    {
      rewrite Heq in Hval1 * => Hval1.
      apply cmra_validN_op_l in Hval1.
      specialize (Hval1 Hin.(inG_id) γ).
      rewrite /iRes_singleton ofe_fun_lookup_singleton lookup_singleton Some_validN in Hval1 *.
      rewrite cmra_transport_validN.
      rewrite auth_validN_eq //=; intuition.
    }
    exists (iRes_singleton γ (◯ a)).
    split.
    * intros i.
      destruct (decide (i = Hin.(inG_id))).
      ** subst.
         rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton.
         intros γ'.
         destruct (decide (γ = γ')).
         { subst. rewrite ?gmap.lookup_op ?gmap.op_singleton.
           rewrite /ma0 in Heq_ma0. rewrite Heq_ma0 ?lookup_singleton //=.
           rewrite ?right_id //= -Some_op Some_validN.
           rewrite -?cmra_transport_op cmra_transport_validN.
           rewrite auth_validN_2; split; eauto.
         }
         { rewrite ?gmap.lookup_op ?gmap.op_singleton.
           rewrite /ma0 in Heq_ma0. rewrite ?lookup_singleton_ne //=.
           rewrite ?right_id ?left_id.
           rewrite Heq in Hval1 * => Heq'.
           apply cmra_validN_op_r in Heq'; eauto.
           eapply Heq'.
         }
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton_ne //=
                 ?left_id ?right_id //=.
    * red => //=. exists y.
      intros i.
      destruct (decide (i = Hin.(inG_id))).
      ** subst.
         rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton.
         rewrite comm assoc. apply cmra_op_ne'; eauto.
         rewrite ?gmap.op_singleton -?cmra_transport_op.
         eapply gmap.singleton_ne, cmra_transport_ne. rewrite comm //=.
      ** rewrite ?ofe_fun_lookup_op /iRes_singleton ?ofe_fun_lookup_singleton_ne //=
                 ?left_id ?right_id //=.
  }
Qed.

Lemma complete_auth_bupd γ a a' b':
  (a,a) ~l~> (a',b') →
  own γ (● a) -∗ <comp> |==> own γ (● a' ⋅ ◯ b').
Proof.
  intros. rewrite complete_auth.
  by apply complete_mono, own_update, auth_update.
Qed.

End auth_complete.

Section crash.

Context {OpT: Type -> Type}.
Context `{Λ: Layer OpT} `{irisG OpT Λ Σ}.

(** crashed(P) should hold if P must hold after a crash step.

   The intuition is that if we are given ownership of all resources needed to
   prove the new state interpretation and the crash interpretation, then we
   should be able to derive the state interpretation and P. This should work for
   something like the encoding of state used in the 'heap_lang' Iris example.

 *)

Definition crashed (P: iProp Σ) : iProp Σ :=
  (∀ σ1 σ2, state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 (Val σ2 tt)⌝
                                                  -∗ <comp> |==> state_interp σ2 ∗ P)%I.


Global Instance crashed_ne n :
  Proper (dist n ==> dist n) (crashed).
Proof. rewrite /crashed => P Q Hequiv. repeat f_equiv; eauto. Qed.

Global Instance crashed_proper:
  Proper ((≡) ==> (≡)) (crashed).
Proof. intros ?? Hequiv. apply equiv_dist=>n; apply crashed_ne; auto. Qed.

Lemma crashed_mono P Q :
  (P -∗ Q) →
  crashed P -∗ crashed Q.
Proof.
  iIntros (HPQ).
  iIntros "Hc". iIntros (σ1 σ2) "H".
  iSpecialize ("Hc" $! σ1 σ2 with "H").
  iApply complete_mono; last by eauto.
  { rewrite -HPQ; reflexivity. }
Qed.

(* TODO: this should be upstreamed. *)
Lemma and_curry: ∀ (PROP : bi) (P Q R : PROP), (P → Q → R)%I ≡ (P ∧ Q → R)%I.
Proof.
  intros.
  apply (anti_symm (⊢)).
  - apply impl_intro_r.
    rewrite and_assoc. by do 2 rewrite impl_elim_l.
  - do 2 apply impl_intro_r. rewrite -and_assoc. apply impl_elim_l.
Qed.

Lemma crashed_plainly P Q:
  crashed P ∗ ■ Q -∗ crashed (P ∗ ■ Q).
Proof.
  iIntros "(Hc&#HQ)".
  iIntros (σ1 σ2) "H".
  iSpecialize ("Hc" $! σ1 σ2 with "H").
  iPoseProof (complete_plainly_sep with "[Hc HQ]") as "H".
  { iFrame. iApply "HQ". }
  iApply complete_mono; last eauto.
  iIntros "(H1&H2)". iMod "H1". iFrame. auto.
Qed.

End crash.