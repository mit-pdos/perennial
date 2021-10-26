From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang.lib Require Import control.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(** A proof principle for if e { do_stuff(); } where do_stuff() is optional and
does something irrelevant to the proof using resources R. Allows to re-use the
proof for both branches, carrying on with resources R. *)
Theorem wp_If_optional stk E (R: iProp Σ) (b: bool) e :
  (∀ (Φ': val → iProp Σ), R -∗ ▷ (R -∗ Φ' #()) -∗ WP e @ stk; E {{ Φ' }}) -∗
  ∀ Φ, R -∗ ▷ (R -∗ Φ #()) -∗ WP If #b e #() @ stk; E {{ Φ }}.
Proof.
  iIntros "Hwp" (Φ) "HR HΦ".
  wp_if_destruct.
  - wp_apply ("Hwp" with "[$HR]").
    iFrame.
  - iApply ("HΦ" with "HR").
Qed.

Theorem wp_If_join (R: iProp Σ) (b: bool) stk E e1 e2 :
  ∀ Φ, (⌜ b = true ⌝ -∗ WP e1 @ stk; E {{ v, ⌜v = #()⌝ ∗ R }}) ∧
       (⌜ b = false ⌝ -∗ WP e2 @ stk; E {{ v, ⌜v = #()⌝ ∗ R }}) -∗
       ▷ (R -∗ Φ #()) -∗ WP if: #b then e1 else e2 @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "Hwp HΦ".
  wp_if_destruct.
  - iDestruct "Hwp" as "[He1 _]".
    iApply (wp_wand with "(He1 [//])").
    iIntros (?) "[-> HR]". by iApply "HΦ".
  - iDestruct "Hwp" as "[_ He2]".
    iApply (wp_wand with "(He2 [//])").
    iIntros (?) "[-> HR]". by iApply "HΦ".
Qed.

(** Designed for [Q] to be left an evar that is resolved with [iNamedAccu] when
finishing the first branch. It may look like the b' is entirely redundant, but
the point is that if at the end of the first branch, your context uses b', then
[iNamedAccu] will use that as a signal to pick a [Q] that uses its argument in
that place -- so you semi-automatically can have terms like [λ b, l ↦ if b then
new_map else old_map ∗ ...].

Unlike [wp_If_join], this deliberately does *not* reduce the [if:], so that you
can use tactics like [case_bool_decide] instead of having to deduce facts from
[bool_decide P = true].

The lemma does not really have anything to do with [if:], it but having an [if:]
in the statement is useful so that [wp_apply] automatically does the right
[wp_bind]. *)
Lemma wp_If_join_evar Q (b : bool) e1 e2 Φ :
  (∀ b', ⌜b' = b⌝ -∗ WP if: #b then e1 else e2 {{ v, ⌜v = #()⌝ ∗ Q b' }}) -∗
  (Q b -∗ Φ #()) -∗ WP if: #b then e1 else e2 {{ Φ }}.
Proof.
  iIntros "Hif Hcont". iApply (wp_wand with "[Hif]").
  - iApply "Hif". done.
  - simpl. iIntros (v) "[-> HQ]". by iApply "Hcont".
Qed.

(** A version of the above for the case where you do not want or need [Q] to
depend on which branch was taken. *)
Lemma wp_If_join_evar' Q (b : bool) e1 e2 Φ :
  (WP if: #b then e1 else e2 {{ v, ⌜v = #()⌝ ∗ Q }}) -∗
  (Q -∗ Φ #()) -∗ WP if: #b then e1 else e2 {{ Φ }}.
Proof.
  iIntros "Hif Hcont". iApply (wp_If_join_evar with "[Hif] Hcont").
  iIntros (? ->). done.
Qed.

Theorem wp_and_pure (P1 P2 : Prop) `{!Decision P1, !Decision P2}
    (e1 e2 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ v, ⌜v = #(bool_decide P1)⌝ }} -∗
  (⌜P1⌝ -∗ WP e2 {{ v, ⌜v = #(bool_decide P2)⌝ }}) -∗
  Φ #(bool_decide (P1 ∧ P2)) -∗
  WP e1 && e2 {{ Φ }}.
Proof.
  iIntros "He1 He2 HΦ".
  wp_bind e1. iApply (wp_wand with "He1").
  iIntros (v1 ->). rewrite (bool_decide_decide P1).
  destruct (decide P1) as [HP1|HP1].
  - wp_pures. iSpecialize ("He2" $! HP1).
    iApply (wp_wand with "He2").
    iIntros (v1 ->).
    rewrite (bool_decide_decide P2).
    destruct (decide P2) as [HP2|HP2].
    + rewrite bool_decide_eq_true_2 //.
    + rewrite bool_decide_eq_false_2 //. tauto.
  - wp_pures. iClear "He2".
    rewrite bool_decide_eq_false_2 //. tauto.
Qed.

(* The first goal (H) is meant to be solved with [iNamedAccu]. *)
Theorem wp_and (P1 P2 : Prop) (H : iProp Σ) `{!Decision P1, !Decision P2}
    (e1 e2 : expr) (Φ : val → iProp Σ) :
  H -∗
  WP e1 {{ v, ⌜v = #(bool_decide P1)⌝ }} -∗
  (⌜P1⌝ -∗ H -∗ WP e2 {{ v, ⌜v = #(bool_decide P2)⌝ ∗ H }}) -∗
  (H -∗ Φ #(bool_decide (P1 ∧ P2))) -∗
  WP e1 && e2 {{ Φ }}.
Proof.
  iIntros "HH He1 He2 HΦ".
  wp_bind e1. iApply (wp_wand with "He1").
  iIntros (v1 ->). rewrite (bool_decide_decide P1).
  destruct (decide P1) as [HP1|HP1].
  - wp_pures. iSpecialize ("He2" $! HP1).
    iSpecialize ("He2" with "HH").
    iApply (wp_wand with "He2").
    iIntros (v1) "[%Hre HH]".
    rewrite Hre.
    rewrite (bool_decide_decide P2).
    destruct (decide P2) as [HP2|HP2].
    + rewrite bool_decide_eq_true_2 //. by iApply "HΦ".
    + rewrite bool_decide_eq_false_2 //; first by iApply "HΦ".
      naive_solver.
  - wp_pures. iClear "He2".
    rewrite bool_decide_eq_false_2 //; first by iApply "HΦ".
    naive_solver.
Qed.

(* The first goal (H) is meant to be solved with [iNamedAccu]. *)
Theorem wp_or (P1 P2 : Prop) (H : iProp Σ) `{!Decision P1, !Decision P2}
    (e1 e2 : expr) (Φ : val → iProp Σ) :
  H -∗
  WP e1 {{ v, ⌜v = #(bool_decide P1)⌝ }} -∗
  (⌜¬ P1⌝ -∗ H -∗ WP e2 {{ v, ⌜v = #(bool_decide P2)⌝ ∗ H }}) -∗
  (H -∗ Φ #(bool_decide (P1 ∨ P2))) -∗
  WP e1 || e2 {{ Φ }}.
Proof.
  iIntros "H He1 He2 HΦ".
  wp_bind e1. iApply (wp_wand with "He1").
  iIntros (v1 ->). rewrite (bool_decide_decide P1).
  destruct (decide P1) as [HP1|HP1].
  - wp_pures. iClear "He2".
    rewrite bool_decide_eq_true_2 //; last tauto. by iApply "HΦ".
  - wp_pures. iSpecialize ("He2" $! HP1 with "H").
    iApply (wp_wand with "He2").
    iIntros (v1) "[-> H]".
    rewrite (bool_decide_decide P2).
    destruct (decide P2) as [HP2|HP2].
    + rewrite bool_decide_eq_true_2 //; last tauto.
      by iApply "HΦ".
    + rewrite bool_decide_eq_false_2 //; last tauto.
      by iApply "HΦ".
Qed.

Theorem wp_or_pure (P1 P2 : Prop) `{!Decision P1, !Decision P2}
    (e1 e2 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ v, ⌜v = #(bool_decide P1)⌝ }} -∗
  (⌜¬ P1⌝ -∗ WP e2 {{ v, ⌜v = #(bool_decide P2)⌝ }}) -∗
  Φ #(bool_decide (P1 ∨ P2)) -∗
  WP e1 || e2 {{ Φ }}.
Proof.
  iIntros "He1 He2 HΦ".
  iApply (wp_or _ _ True with "[//] He1 [He2]").
  { iIntros "HP _". iApply (wp_wand with "(He2 HP)"). eauto. }
  eauto.
Qed.

Theorem wp_Assume stk E (cond: bool) :
  {{{ True }}}
    Assume #cond @ stk; E
  {{{ RET #(); ⌜cond = true⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - iApply ("HΦ" with "[//]").
  - wp_pures.
    iLöb as "IH".
    wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

Theorem wp_Assert stk E (cond: bool) :
  cond = true ->
  {{{ True }}}
    Assert #cond @ stk; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  wp_call.
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
