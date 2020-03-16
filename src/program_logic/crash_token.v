From iris.algebra Require Import auth agree excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition crashR := csumR (exclR unitO) (agreeR unitO).
Definition NC_tok : crashR := Cinl (Excl ()).
Definition C_tok : crashR := Cinr (to_agree ()).

Class crashG Σ := { crash_inG :> inG Σ crashR; crash_name : gname }.
Class crashPreG Σ := { crash_inPreG :> inG Σ crashR }.

Definition crashΣ : gFunctors :=
    #[GFunctor (csumR (exclR unitO) (agreeR unitO))].

Instance subG_crashG {Σ} : subG crashΣ Σ → crashPreG Σ.
Proof. solve_inG. Qed.

Definition NC_def `{crashG Σ} := own crash_name NC_tok.
Definition NC_aux `{crashG Σ} : seal NC_def. by eexists. Qed.
Definition NC `{crashG Σ} := NC_aux.(unseal).
Definition C_def `{crashG Σ} := own crash_name C_tok.
Definition C_aux `{crashG Σ} : seal C_def. by eexists. Qed.
Definition C `{crashG Σ} := C_aux.(unseal).

Lemma NC_alloc `{!crashPreG Σ} : ⊢ |==> ∃ _ : crashG Σ, NC.
Proof.
  iIntros.
  iMod (own_alloc (Cinl (Excl ()))) as (γ) "H".
  { econstructor. }
  iExists {| crash_name := γ |}.
  rewrite /NC NC_aux.(seal_eq). by iFrame.
Qed.

Section crash_tok_props.
Context `{!crashG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance C_timeless : Timeless C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance C_persistent : Persistent C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance NC_timeless : Timeless NC.
Proof. rewrite /NC NC_aux.(seal_eq). apply _. Qed.

Lemma NC_C: NC -∗ C -∗ False.
Proof.
 rewrite /C C_aux.(seal_eq).
 rewrite /NC NC_aux.(seal_eq).
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma NC_upd_C: NC ==∗ C.
Proof.
 rewrite /C C_aux.(seal_eq).
 rewrite /NC NC_aux.(seal_eq).
 iIntros "H". iMod (own_update with "H") as "$".
 { by apply cmra_update_exclusive. }
 done.
Qed.
End crash_tok_props.
