From iris.algebra Require Import auth.
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Import weakestpre.
From Perennial.algebra Require Import auth_frac.
Set Default Proof Using "Type".

(* Algebras to help with circular buffer proof *)

(* fmcounter = Fractional monotone counter *)
Definition fmcounterUR := authUR mnatUR.
Class fmcounterG Σ :=
  { fmcounter_inG :> inG Σ fmcounterUR }.

Section fmc_props.
Context `{fmcounterG Σ}.

Definition fmcounter γ q n := own γ (●{q} n).
Definition fmcounter_lb γ n := own γ (◯ n).

Lemma fmcounter_agree_1 γ q1 q2 n1 n2:
  fmcounter γ q1 n1 -∗ fmcounter γ q2 n2 -∗ ⌜ n1 = n2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  by apply auth_auth_frac_op_inv in Hval.
Qed.

Lemma fmcounter_agree_2 γ q1 n1 n2:
  fmcounter γ q1 n1 -∗ fmcounter_lb γ n2 -∗ ⌜ n2 ≤ n1 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  by apply auth_both_frac_valid in Hval as (?&Hle%mnat_included&?).
Qed.

Lemma fmcounter_lb_mono γ n1 n2:
  n1 ≤ n2 ->
  fmcounter_lb γ n2 -∗ fmcounter_lb γ n1.
Proof.
  iIntros (Hle) "Hlb".
  rewrite /fmcounter_lb.
  iApply (own_mono with "Hlb").
  apply @auth_frag_mono.
  apply mnat_included; auto.
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
  iMod (own_update _ _ ((●{q} n) ⋅ ◯ n) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmcounter_get_lb γ q n:
  fmcounter γ q n ==∗ fmcounter γ q n ∗ fmcounter_lb γ n.
Proof.
  iIntros "Hm".
  iMod (own_update _ _ ((●{q} n) ⋅ ◯ n) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmcounter_update n' γ n:
  n <= n' ->
  fmcounter γ 1 n ==∗ fmcounter γ 1 n' ∗ fmcounter_lb γ n'.
Proof.
  iIntros (Hlt) "Hm".
  iMod (own_update with "Hm") as "($&?)"; last done.
  apply auth_update_alloc, mnat_local_update; auto.
Qed.

Lemma fmcounter_alloc n :
  ⊢ |==> ∃ γ, fmcounter γ 1 n.
Proof.
  iStartProof.
  iMod (own_alloc (●{1} n)) as (γ) "H".
  { apply auth_auth_valid.
    cbv; auto. (* TODO: better way to prove an mnat is valid? *) }
  iModIntro.
  iExists _; iFrame.
Qed.

Global Instance fmcounter_lb_pers γ n: Persistent (fmcounter_lb γ n).
Proof. apply _. Qed.

Global Instance fmcounter_fractional γ n: Fractional (λ q, fmcounter γ q n).
Proof. intros p q. apply fmcounter_sep. Qed.

Global Instance fmcounter_as_fractional γ q n :
  AsFractional (fmcounter γ q n) (λ q, fmcounter γ q n) q.
Proof. split; first by done. apply _. Qed.

Global Instance fmcounter_into_sep γ n :
  IntoSep (fmcounter γ 1 n) (fmcounter γ (1/2) n) (fmcounter γ (1/2) n).
Proof. apply _. Qed.

End fmc_props.
