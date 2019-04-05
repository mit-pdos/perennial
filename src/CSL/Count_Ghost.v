From iris.algebra Require Import auth agree functions csum cmra.
From RecoveryRefinement.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Export CSL.Refinement CSL.NamedDestruct ExMach.WeakestPre CSL.ProofModeClasses.
Require Eqdep.
Import uPred.

Class ghost_mapG (A: ofeT) Σ `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A} :=
  { ghost_map_inG :> inG Σ (authR (optionUR (prodR countingR (agreeR A)))) }.

Definition ghost_mapΣ (A: ofeT) `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A} : gFunctors :=
  #[GFunctor (authR (optionUR (prodR countingR (agreeR A))))].

Instance subG_ghost_mapG (A: ofeT) Σ `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A} :
  subG (ghost_mapΣ A) Σ → ghost_mapG A Σ.
Proof. solve_inG. Qed.

Section ghost_var_helpers.
Context {A: ofeT} `{hGMG: @ghost_mapG A Σ H1 H2}.


Definition ghost_mapsto (γ: gname) (n: Z) (v : A) : iProp Σ :=
  (own γ (◯ Some (Count n, to_agree v)))%I.
Definition ghost_mapsto_auth (γ: gname) (v : A) : iProp Σ :=
  (own γ (● Some (Count 0, to_agree v))).
End ghost_var_helpers.

Local Notation "l ●↦ v" := (ghost_mapsto_auth l v)
  (at level 20, format "l  ●↦  v") : bi_scope.
Local Notation "l ↦{ q } v" := (ghost_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (ghost_mapsto l 0 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{0} -)%I (at level 20) : bi_scope.

Section ghost_var_helpers.
Context {A} {Σ}  `{ghost_mapG A Σ}.

Lemma ghost_var_alloc (a: A):
  (|==> ∃ γ, γ ●↦ a ∗ γ ↦ a)%I.
Proof.
  iMod (own_alloc (● (Some (Count 0, to_agree a)) ⋅
                   ◯ (Some (Count 0, to_agree a))))
    as (γ) "[H1 H2]".
  { apply auth_valid_discrete_2; split; eauto. split; econstructor. }
  iModIntro. iExists γ. iFrame.
Qed.


Lemma ghost_var_agree γ (a1 a2: A) q :
  γ ●↦ a1 -∗ γ ↦{q} a2 -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  apply auth_valid_discrete_2 in Hval as (Hincl&?).
  apply option_included in Hincl as [|(p1&p2&Heq1&Heq2&Hcase)]; first by congruence.
  inversion Heq1; subst. inversion Heq2; subst.
  destruct Hcase as [(Heq1'&Heq2')|Hincl].
  - apply to_agree_inj in Heq2'. eauto.
  - apply prod_included in Hincl as (?&Heq2'%to_agree_included); eauto.
Qed.

Lemma ghost_var_agree2 γ (a1 a2: A) q1 q2 :
  γ ↦{q1} a1 -∗ γ ↦{q2} a2 -∗ ⌜ a1 = a2 ⌝.
Proof.
  apply wand_intro_r.
  rewrite -own_op -auth_frag_op own_valid discrete_valid.
  f_equiv=> /auth_own_valid /=.
  rewrite -Some_op pair_op.
  intros [_ Heq%agree_op_invL']. eauto.
Qed.

Lemma read_split_join γ (n: nat) (v: A):
  γ ↦{n} v ⊣⊢ γ ↦{S n} v ∗ γ ↦{-1} v.
Proof.
  rewrite -own_op -auth_frag_op /ghost_mapsto.
  f_equiv. rewrite -Some_op ?pair_op.
  rewrite counting_op' //=.
  replace (S n + (-1))%Z with (n : Z) by lia.
  assert (0 ⋅ S n = (S n)) as Hop by auto.
  replace (S n + (-1))%Z with (n : Z) by lia.
  repeat (destruct (decide)); try lia.
  rewrite agree_idemp //=.
Qed.

Lemma ghost_var_update γ (a1' a1 a2 : A) :
  γ ●↦ a1 -∗ γ ↦ a2 ==∗ γ ●↦ a1' ∗ γ ↦ a1'.
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _
                     (● (Some (Count 0, to_agree a1')) ⋅
                      ◯ (Some (Count 0, to_agree a1')))
                        with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

Lemma named_ghost_var_update γ (a1' a1 a2 : A) i1 i2 :
  named i1 (γ ●↦ a1) -∗ named i2 (γ ↦ a2)
        ==∗ named i1 (γ ●↦ a1') ∗ named i2 (γ ↦ a1').
Proof. unbundle_names; apply ghost_var_update. Qed.

End ghost_var_helpers.


From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Ltac unify_ghost :=
  match goal with
  | [ |- context[ environments.Esnoc _ ?auth_name (?y ●↦ ?x)] ] =>
    match goal with
    | [ |- context[ ghost_mapsto y _ x ] ] => fail 1
    | [ |- context[ environments.Esnoc _ ?frag_name (y ↦{?q} ?z)] ] =>
      let pat := constr:([(SIdent auth_name nil); (SIdent frag_name nil)]) in
      (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
    end
  end.

Module test.
Section test.
Context {Σ} `{ghost_mapG A Σ}.
Lemma test γ q (v1 v2: A) : γ ●↦ v1 -∗ γ ↦{q} v2 -∗ ⌜ v1 = v2 ⌝.
Proof. iIntros "H1 H2". by unify_ghost. Qed.
End test.
End test.