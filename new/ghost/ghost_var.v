(* Slightly modified version https://gitlab.mpi-sws.org/iris/iris/-/blob/849f50f421114ad1b8caf0cd1b66aff338e4abfa/iris/base_logic/lib/ghost_var.v *)
From New.experiments Require Export own.

(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)
(* From iris.algebra Require Import dfrac_agree proofmode_classes frac. *)
From iris.bi.lib Require Import fractional.
(* From iris.proofmode Require Import proofmode. *)
(* From iris.base_logic.lib Require Export own. *)
(* From iris.prelude Require Import options. *)

Local Definition ghost_var_def `{!allG Σ} {A : Type}
    (γ : gname) (q : Qp) (a : A) : iProp Σ :=
  own γ (to_frac_agree (A:=leibnizO A) q a).
Local Definition ghost_var_aux : seal (@ghost_var_def). Proof. by eexists. Qed.
Definition ghost_var := ghost_var_aux.(unseal).
Local Definition ghost_var_unseal :
  @ghost_var = @ghost_var_def := ghost_var_aux.(seal_eq).
Global Arguments ghost_var {Σ _ A} γ q a.

Local Ltac unseal := rewrite ?ghost_var_unseal /ghost_var_def.

Section lemmas.
  Context `{!allG Σ} {A : Type}.
  Implicit Types (a b : A) (q : Qp).

  Global Instance ghost_var_timeless γ q a : Timeless (ghost_var γ q a).
  Proof. unseal. apply _. Qed.

  Global Instance ghost_var_fractional γ a : Fractional (λ q, ghost_var γ q a).
  Proof. intros q1 q2. unseal. rewrite -own_op -frac_agree_op //. Qed.
  Global Instance ghost_var_as_fractional γ a q :
    AsFractional (ghost_var γ q a) (λ q, ghost_var γ q a) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma ghost_var_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_var γ 1 a.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.
  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, ghost_var γ 1 a.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma ghost_var_valid_2 γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %[Hq Ha]%frac_agree_op_valid.
    done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_var_agree γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (ghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.

  Global Instance ghost_var_combine_gives γ a1 q1 a2 q2 :
    CombineSepGives (ghost_var γ q1 a1) (ghost_var γ q2 a2)
      ⌜(q1 + q2 ≤ 1)%Qp ∧ a1 = a2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Global Instance ghost_var_combine_as γ a1 q1 a2 q2 q :
    IsOp q q1 q2 →
    CombineSepAs (ghost_var γ q1 a1) (ghost_var γ q2 a2)
      (ghost_var γ q a1) | 60.
  (* higher cost than the Fractional instance, which is used for a1 = a2 *)
  Proof.
    rewrite /CombineSepAs /IsOp => ->. iIntros "[H1 H2]".
    (* This can't be a single [iCombine] since the instance providing that is
    exactly what we are proving here. *)
    iCombine "H1 H2" gives %[_ ->].
    by iCombine "H1 H2" as "H".
  Qed.

  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma ghost_var_split γ a q1 q2 :
    ghost_var γ (q1 + q2) a -∗ ghost_var γ q1 a ∗ ghost_var γ q2 a.
  Proof. iIntros "[$$]". Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    ghost_var γ 1 a ==∗ ghost_var γ 1 b.
  Proof.
    unseal. iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    intros Hq. unseal. rewrite -own_op. iApply own_update_2.
    apply frac_agree_update_2. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 -∗
    ghost_var γ (1/2) a2 ==∗
    ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp.half_half. Qed.

  (** Framing support *)
  Global Instance frame_ghost_var p γ a q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (ghost_var γ q1 a) (ghost_var γ q2 a) (ghost_var γ q a) | 5.
  Proof. apply: frame_fractional. Qed.

End lemmas.
