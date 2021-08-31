From iris.algebra Require Import auth agree excl csum.
From iris.proofmode Require Import tactics.
From Perennial.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Definition crashR := csumR fracR (agreeR unitO).
Definition NC_tok q : crashR := Cinl q.
Definition C_tok : crashR := Cinr (to_agree ()).

Class crashGS Σ := { crash_inG :> inG Σ crashR; crash_name : gname }.
Class crashGpreS Σ := { crash_inPreG :> inG Σ crashR }.

Definition crashΣ : gFunctors :=
    #[GFunctor (csumR fracR (agreeR unitO))].

Global Instance subG_crashGS {Σ} : subG crashΣ Σ → crashGpreS Σ.
Proof. solve_inG. Qed.

Definition NC_def `{crashGS Σ} q := own crash_name (NC_tok q).
Definition NC_aux `{crashGS Σ} : seal NC_def. by eexists. Qed.
Definition NC `{crashGS Σ} := NC_aux.(unseal).
Global Arguments NC {_ _} _%Qp.
Definition C_def `{crashGS Σ} := own crash_name C_tok.
Definition C_aux `{crashGS Σ} : seal C_def. by eexists. Qed.
Definition C `{crashGS Σ} := C_aux.(unseal).

Lemma NC_alloc `{!crashGpreS Σ} : ⊢ |==> ∃ _ : crashGS Σ, NC 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iExists {| crash_name := γ |}.
  rewrite /NC NC_aux.(seal_eq). by iFrame.
Qed.

Lemma NC_alloc_strong `{!crashGpreS Σ} :
  ⊢ |==> ∃ γn : gname, let Hc := {| crash_name := γn |} in NC 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iExists γ.
  rewrite /NC NC_aux.(seal_eq). by iFrame.
Qed.

Section crash_tok_props.
Context `{!crashGS Σ}.
Implicit Types i : positive.
Implicit Types P Q R : iProp Σ.

Global Instance C_timeless : Timeless C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance C_persistent : Persistent C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance NC_timeless q : Timeless (NC q).
Proof. rewrite /NC NC_aux.(seal_eq). apply _. Qed.

Lemma NC_split q:
  NC q ⊢ NC (q/2) ∗ NC (q/2).
Proof. by rewrite /NC NC_aux.(seal_eq) -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma NC_join q:
  NC (q/2) ∗ NC (q/2) ⊢ NC q.
Proof. by rewrite /NC NC_aux.(seal_eq) -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma NC_C q: NC q -∗ C -∗ False.
Proof.
 rewrite /C C_aux.(seal_eq).
 rewrite /NC NC_aux.(seal_eq).
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma NC_upd_C: NC 1 ==∗ C.
Proof.
 rewrite /C C_aux.(seal_eq).
 rewrite /NC NC_aux.(seal_eq).
 iIntros "H". iMod (own_update with "H") as "$".
 { by apply cmra_update_exclusive. }
 done.
Qed.
End crash_tok_props.
