From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import iprop own.
From Perennial.program_logic Require Import ghost_var.
Set Default Proof Using "Type".

(** resources for locking a resource but then retrieving it temporarily from a
single thread that is allowed to access it *)

Class thread_ownG Σ :=
  { thread_own_ghost_bool :> ghost_varG Σ bool; }.

Inductive OwnStatus := Available | Used.

Section thread_owned.
Context {Σ: gFunctors}.
Context `{!thread_ownG Σ}.
Implicit Types (γ:gname) (P:iProp Σ).

Definition thread_own_ctx γ P: iProp Σ :=
  ∃ (available: bool),
    ghost_var γ (1/2) available ∗ if available then P else emp.

Definition thread_own γ (s:OwnStatus) : iProp Σ :=
  ghost_var γ (1/2) (if s then true else false).

Global Instance thread_own_ctx_timeless γ P `{!Timeless P} : Timeless (thread_own_ctx γ P).
Proof.
  rewrite /thread_own_ctx.
  apply bi.exist_timeless; intros.
  destruct x; apply _.
Qed.

Global Instance thread_own_timeless γ s : Timeless (thread_own γ s) := _.

Theorem thread_own_alloc P :
  P -∗ |==> ∃ γ, thread_own_ctx γ P ∗ thread_own γ Available.
Proof.
  iIntros "HP".
  iMod (ghost_var_alloc true) as (γ) "[Hγ Hown]".
  iModIntro.
  iExists γ.
  iFrame.
  iExists true; iFrame.
Qed.

Theorem thread_own_get γ P :
  thread_own_ctx γ P -∗
  thread_own γ Available ==∗
  thread_own_ctx γ P ∗
  P ∗ thread_own γ Used.
Proof.
  rewrite /thread_own.
  iIntros "Hctx Hγ".
  iDestruct "Hctx" as (available) "(Hown&HP)".
  unify_ghost_var γ. iFrame.
  iMod (ghost_var_update_halves false with "Hγ Hown") as "($&Hown)".
  iModIntro.
  iExists false; iFrame.
Qed.

Theorem thread_own_put {γ} P' P :
  thread_own_ctx γ P -∗
  thread_own γ Used -∗
  P' ==∗ thread_own_ctx γ P' ∗ thread_own γ Available.
Proof.
  rewrite /thread_own.
  iIntros "Hctx Hγ HP'".
  iDestruct "Hctx" as (available) "(Hown&_)".
  iMod (ghost_var_update_halves true with "Hγ Hown") as "($&Hown)".
  iModIntro.
  iExists true; iFrame.
Qed.

Theorem thread_own_put_same {γ} P :
  thread_own_ctx γ P -∗
  thread_own γ Used -∗
  P ==∗ thread_own_ctx γ P ∗ thread_own γ Available.
Proof.
  iIntros "Hctx Hused HP".
  iMod (thread_own_put P with "Hctx Hused HP") as "[$ $]".
  auto.
Qed.

End thread_owned.

Global Opaque thread_own_ctx thread_own.
