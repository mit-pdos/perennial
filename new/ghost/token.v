(* Slightly modified version https://gitlab.mpi-sws.org/iris/iris/-/blob/849f50f421114ad1b8caf0cd1b66aff338e4abfa/iris/base_logic/lib/token.v *)
From New.ghost Require Export own.

(** This library provides assertions that represent "unique tokens".
The [token γ] assertion provides ownership of the token named [γ],
and the key lemma [token_exclusive] proves only one token exists. *)
(* From iris.algebra Require Import excl. *)
(* From iris.proofmode Require Import proofmode. *)
(* From iris.base_logic.lib Require Export own. *)
(* From iris.prelude Require Import options. *)

Local Definition token_def `{!allG Σ} (γ : gname) : iProp Σ :=
  own γ (Excl ()).
Local Definition token_aux : seal (@token_def). Proof. by eexists. Qed.
Definition token := token_aux.(unseal).
Local Definition token_unseal :
  @token = @token_def := token_aux.(seal_eq).
Global Arguments token {Σ _} γ.

Local Ltac unseal := rewrite ?token_unseal /token_def.

Section lemmas.
  Context `{!allG Σ}.

  Global Instance token_timeless γ : Timeless (token γ).
  Proof. unseal. apply _. Qed.

  Lemma token_alloc_strong (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token γ.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.
  Lemma token_alloc :
    ⊢ |==> ∃ γ, token γ.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma token_exclusive γ :
    token γ -∗ token γ -∗ False.
  Proof.
    unseal. iIntros "Htok1 Htok2".
    iCombine "Htok1 Htok2" gives %[].
  Qed.
  Global Instance token_combine_gives γ :
    CombineSepGives (token γ) (token γ) ⌜False⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (token_exclusive with "H1 H2") as %[].
  Qed.

End lemmas.
