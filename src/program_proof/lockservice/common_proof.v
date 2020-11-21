From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From stdpp Require Import gmap.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From iris.algebra Require Import numbers.
From Coq.Structures Require Import OrdersTac.
From Perennial.program_proof.lockservice Require Import lockservice nondet.

Section common_proof.
Context `{!heapG Σ}.

(* This spec is delibertaely weaker than the implementation. *)
Lemma nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam. iApply "HΦ". eauto.
Qed.

Lemma overflow_guard_incr_spec stk E (v:u64) : 
{{{ True }}}
  overflow_guard_incr #v @ stk ; E
{{{
     RET #(); ⌜((int.Z v) + 1 = int.Z (word.add v 1))%Z⌝
}}}.
Proof.
  iIntros (Φ) "_ Hpost".
  wp_lam. wp_pures.
  wp_forBreak_cond.
  wp_pures.
  destruct bool_decide eqn:Hineq.
  {
    apply bool_decide_eq_true in Hineq.
    wp_pures. iLeft. by iFrame.
  }
  {
    apply bool_decide_eq_false in Hineq.
    wp_pures. iRight. iSplitR; first done.
    iApply "Hpost". iPureIntro.
    assert (int.Z (word.add v 1) >= int.Z v)%Z by lia.
    destruct (bool_decide ((int.Z v) + 1 < 2 ^ 64 ))%Z eqn:Hnov.
    {
      apply bool_decide_eq_true in Hnov.
      word.
    }
    apply bool_decide_eq_false in Hnov.
    assert (int.Z v + (int.Z 1) >= 2 ^ 64)%Z.
    { replace (int.Z 1)%Z with (1)%Z by word. lia. }
    apply sum_overflow_check in H0.
    contradiction.
  }
Qed.

End common_proof.
