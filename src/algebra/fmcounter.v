From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.algebra Require Import auth_frac own_discrete.
Set Default Proof Using "Type".

(* Algebras to help with circular buffer proof *)

(* TODO: replace by upstream Iris own_mnat *)

(* fmcounter = Fractional monotone counter *)
Definition fmcounterUR := authUR max_natUR.
Class fmcounterG Σ :=
  { fmcounter_inG :> inG Σ fmcounterUR }.

Section fmc_props.
Context `{fmcounterG Σ}.

Definition fmcounter γ q (n: nat) := own γ (●{q} (MaxNat n)).
Definition fmcounter_lb γ (n: nat) := own γ (◯ (MaxNat n)).

Instance inj_MaxNat_equiv : Inj eq equiv MaxNat.
Proof.
  intros n1 n2.
  intros ?%leibniz_equiv.
  inversion H1; auto.
Qed.

Lemma fmcounter_agree_1 γ q1 q2 n1 n2:
  fmcounter γ q1 n1 -∗ fmcounter γ q2 n2 -∗ ⌜ n1 = n2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  apply auth_auth_frac_op_inv in Hval.
  iPureIntro.
  apply (inj MaxNat); auto.
Qed.

Lemma fmcounter_agree_2 γ q1 (n1 n2: nat) :
  fmcounter γ q1 n1 -∗ fmcounter_lb γ n2 -∗ ⌜ n2 ≤ n1 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  by apply auth_both_frac_valid_discrete in Hval as (?&Hle%max_nat_included&?).
Qed.

Lemma fmcounter_lb_mono γ n1 n2:
  n1 ≤ n2 ->
  fmcounter_lb γ n2 -∗ fmcounter_lb γ n1.
Proof.
  iIntros (Hle) "Hlb".
  rewrite /fmcounter_lb.
  iApply (own_mono with "Hlb").
  apply @auth_frag_mono.
  apply max_nat_included; auto.
Qed.

Lemma fmcounter_sep γ q1 q2 n:
  fmcounter γ (q1 + q2) n ⊣⊢ fmcounter γ q1 n ∗ fmcounter γ q2 n.
Proof.
  iSplit.
  - iIntros "(Hm1&Hm2)". iFrame.
  - iIntros "(Hm1&Hm2)". iCombine "Hm1 Hm2" as "$".
Qed.

Lemma fmcounter_to_lb γ q n:
  fmcounter γ q n ==∗ fmcounter_lb γ n.
Proof.
  iIntros "Hm".
  iMod (own_update _ _ ((●{q} (MaxNat n)) ⋅ ◯ (MaxNat n)) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmcounter_get_lb γ q n:
  fmcounter γ q n ==∗ fmcounter γ q n ∗ fmcounter_lb γ n.
Proof.
  iIntros "Hm".
  iMod (own_update _ _ ((●{q} (MaxNat n)) ⋅ ◯ (MaxNat n)) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmcounter_update n' γ n:
  n <= n' ->
  fmcounter γ 1 n ==∗ fmcounter γ 1 n' ∗ fmcounter_lb γ n'.
Proof.
  iIntros (Hlt) "Hm".
  iMod (own_update with "Hm") as "($&?)"; last done.
  apply auth_update_alloc, max_nat_local_update; auto.
Qed.

Lemma fmcounter_alloc n :
  ⊢ |==> ∃ γ, fmcounter γ 1 n.
Proof.
  iStartProof.
  iMod (own_alloc (●{1} (MaxNat n))) as (γ) "H".
  { apply auth_auth_valid.
    cbv; auto. (* TODO: better way to prove an mnat is valid? *) }
  iModIntro.
  iExists _; iFrame.
Qed.

Lemma fmcounter_update_halves (γ: gname) (n1 n2 n': nat) :
  (n1 ≤ n')%nat →
  fmcounter γ (1/2) n1 -∗
  fmcounter γ (1/2) n2 -∗
  |==> fmcounter γ (1/2) n' ∗
     fmcounter γ (1/2) n' ∗
     fmcounter_lb γ n'.
Proof.
  iIntros (Hle) "Hn1 Hn2".
  iDestruct (fmcounter_agree_1 with "Hn1 Hn2") as %<-.
  iDestruct (fmcounter_sep with "[$Hn1 $Hn2]") as "Hn".
  rewrite Qp_half_half.
  iMod (fmcounter_update _ _ _ Hle with "Hn") as "([Hn1 Hn2]&$)".
  iModIntro.
  iFrame.
Qed.

Global Instance fmcounter_lb_pers γ n: Persistent (fmcounter_lb γ n).
Proof. apply _. Qed.

Global Instance fmcounter_lb_timeless γ n: Timeless (fmcounter_lb γ n).
Proof. apply _. Qed.

Global Instance fmcounter_timeless γ q n: Timeless (fmcounter γ q n).
Proof. apply _. Qed.

Global Instance fmcounter_fractional γ n: Fractional (λ q, fmcounter γ q n).
Proof. intros p q. apply fmcounter_sep. Qed.

Global Instance fmcounter_as_fractional γ q n :
  AsFractional (fmcounter γ q n) (λ q, fmcounter γ q n) q.
Proof. split; first by done. apply _. Qed.

Global Instance fmcounter_into_sep γ n :
  IntoSep (fmcounter γ 1 n) (fmcounter γ (1/2) n) (fmcounter γ (1/2) n).
Proof. apply _. Qed.

Global Instance fmcounter_discretizable γ q n: Discretizable (fmcounter γ q n).
Proof. apply _. Qed.

Global Instance fmcounter_lb_discretizable γ n: Discretizable (fmcounter_lb γ n).
Proof. apply _. Qed.

End fmc_props.

Typeclasses Opaque fmcounter fmcounter_lb.
