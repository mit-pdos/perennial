From iris.bi Require Export bi.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

(** The class of absolutely laterable assertions *)
Class AbsLaterable {PROP : bi} (P : PROP) := abs_laterable :
  ⊢ (∃ Q, □ (▷ Q ∗-∗ ◇ P)).
Arguments AbsLaterable {_} _%I : simpl never.
Arguments abs_laterable {_} _%I {_}.
Global Hint Mode AbsLaterable + ! : typeclass_instances.

Section instances.
  Context {PROP : bi}.
  Implicit Types P : PROP.
  Implicit Types Ps : list PROP.

  Global Instance abs_laterable_proper : Proper ((⊣⊢) ==> (↔)) (@AbsLaterable PROP).
  Proof. solve_proper. Qed.

  Global Instance later_abs_laterable P : AbsLaterable (▷ P).
  Proof.
    rewrite /AbsLaterable. iExists P.
    iIntros "!>"; iSplit.
    - iIntros "HP". iModIntro. eauto.
    - iIntros "H". by iApply bi.except_0_later.
  Qed.

  Global Instance timeless_abs_laterable P :
    Timeless P → AbsLaterable P.
  Proof.
    rewrite /AbsLaterable. iIntros (?). iExists P%I.
    iIntros "!>"; iSplit.
    - by iIntros ">HP !>".
    - by iIntros ">HP".
  Qed.

  Global Instance sep_abs_laterable P Q :
    AbsLaterable P → AbsLaterable Q → AbsLaterable (P ∗ Q).
  Proof.
    rewrite /AbsLaterable. iIntros (LP LQ).
    iDestruct (LP) as (P') "#HP".
    iDestruct (LQ) as (Q') "#HQ".
    iExists (P' ∗ Q')%I.
    iIntros "!>"; iSplit; iIntros "[HP' HQ']"; iSplitL "HP'".
    - iApply "HP". done.
    - iApply "HQ". done.
    - iApply "HP". done.
    - iApply "HQ". done.
  Qed.

  Global Instance big_sepL_abs_laterable Ps :
    Timeless (PROP:=PROP) emp →
    TCForall AbsLaterable Ps →
    AbsLaterable ([∗] Ps).
  Proof. induction 2; simpl; apply _. Qed.

End instances.
