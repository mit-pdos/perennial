(** FIXME: probably want notation, and eventually want to use
an upstreamed version of dghost_var with dfrac. *)

(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)
From New.ghost Require Export own.
From Perennial.iris_lib Require Import dfractional.
From Perennial.goose_lang Require Import ipersist.
From iris.bi.lib Require Import fractional.

Local Definition dghost_var_def `{!allG Σ} {A}
    (γ : gname) (dq : dfrac) (a : A) : iProp Σ :=
  own γ (to_dfrac_agree (A:=leibnizO A) dq a).
Local Definition dghost_var_aux : seal (@dghost_var_def). Proof. by eexists. Qed.
Definition dghost_var := dghost_var_aux.(unseal).
Local Definition dghost_var_unseal :
  @dghost_var = @dghost_var_def := dghost_var_aux.(seal_eq).
Global Arguments dghost_var {Σ _ A} γ dq a.

Local Ltac unseal := rewrite ?dghost_var_unseal /dghost_var_def.

Section lemmas.
  Context `{!allG Σ} {A : Type}.
  Implicit Types (a b : A) (dq : dfrac).

  Global Instance dghost_var_timeless γ dq a : Timeless (dghost_var γ dq a).
  Proof. unseal. apply _. Qed.

  #[global]
  Instance dghost_var_dfractional γ a :
    DFractional (λ dq, dghost_var γ dq a).
  Proof.
    unseal. split.
    - intros. rewrite dfrac_agree_op own_op //.
    - apply _.
    - intros. iApply own_update. apply dfrac_agree_persist.
  Qed.

  #[global]
  Instance dghost_var_as_dfractional γ dq a :
    AsDFractional (dghost_var γ dq a) (λ dq, dghost_var γ dq a) dq.
  Proof. auto. Qed.

  #[global]
  Instance dghost_var_as_fractional γ q a :
    AsFractional (dghost_var γ (DfracOwn q) a)
      (λ q, dghost_var γ (DfracOwn q) a) q.
  Proof.
    constructor; [done|]. intros ??.
    unseal. rewrite -own_op -frac_agree_op //.
  Qed.

  Lemma dghost_var_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ dghost_var γ (DfracOwn 1) a.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.

  Lemma dghost_var_alloc a :
    ⊢ |==> ∃ γ, dghost_var γ (DfracOwn 1) a.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma dghost_var_valid_2 γ a1 dq1 a2 dq2 :
    dghost_var γ dq1 a1 -∗ dghost_var γ dq2 a2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %[Hq Ha]%dfrac_agree_op_valid.
    done.
  Qed.

  (** Almost all the time, this is all you really need. *)
  Lemma dghost_var_agree γ a1 dq1 a2 dq2 :
    dghost_var γ dq1 a1 -∗ dghost_var γ dq2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (dghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.

  Global Instance dghost_var_combine_gives γ a1 dq1 a2 dq2 :
    CombineSepGives (dghost_var γ dq1 a1) (dghost_var γ dq2 a2)
      ⌜(✓ (dq1 ⋅ dq2)) ∧ a1 = a2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (dghost_var_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Global Instance dghost_var_combine_as γ a1 dq1 a2 dq2 dq :
    IsOp dq dq1 dq2 →
    CombineSepAs (dghost_var γ dq1 a1) (dghost_var γ dq2 a2)
      (dghost_var γ dq a1) | 60.
  (* higher cost than the Fractional instance, which is used for a1 = a2 *)
  Proof.
    rewrite /CombineSepAs /IsOp => ->. iIntros "[H1 H2]".
    (* This can't be a single [iCombine] since the instance providing that is
    exactly what we are proving here. *)
    iCombine "H1 H2" gives %[_ ->].
    unseal. iCombine "H1 H2" as "H".
    by rewrite dfrac_agree_op.
  Qed.

  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma dghost_var_split γ a dq1 dq2 :
    dghost_var γ (dq1 ⋅ dq2) a -∗ dghost_var γ dq1 a ∗ dghost_var γ dq2 a.
  Proof.
    unseal. rewrite dfrac_agree_op. iIntros "[$$]".
  Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma dghost_var_update b γ a :
    dghost_var γ (DfracOwn 1) a ==∗ dghost_var γ (DfracOwn 1) b.
  Proof.
    unseal. iApply own_update. apply cmra_update_exclusive. done.
  Qed.

  Lemma dghost_var_update_2 b γ a1 dq1 a2 dq2 :
    (dq1 ⋅ dq2 = DfracOwn 1)%Qp →
    dghost_var γ dq1 a1 -∗ dghost_var γ dq2 a2 ==∗ dghost_var γ dq1 b ∗ dghost_var γ dq2 b.
  Proof.
    intros Hq. unseal. rewrite -own_op. iApply own_update_2.
    apply dfrac_agree_update_2. done.
  Qed.

  Lemma dghost_var_update_halves b γ a1 a2 :
    dghost_var γ (DfracOwn (1/2)) a1 -∗ dghost_var γ (DfracOwn (1/2)) a2 ==∗ dghost_var γ (DfracOwn (1/2)) b ∗ dghost_var γ (DfracOwn (1/2)) b.
  Proof.
    apply dghost_var_update_2.
    rewrite dfrac_op_own.
    rewrite Qp.half_half //.
  Qed.

  Lemma dghost_var_persist γ q a :
    dghost_var γ (DfracOwn q) a ==∗ dghost_var γ DfracDiscarded a.
  Proof. iIntros "H". by iPersist "H". Qed.

  (** Framing support *)
  Global Instance frame_dghost_var p γ a q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (dghost_var γ (DfracOwn q1) a) (dghost_var γ (DfracOwn q2) a) (dghost_var γ (DfracOwn q) a) | 5.
  Proof. apply: frame_fractional. Qed.

End lemmas.
