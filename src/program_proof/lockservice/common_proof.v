From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof.lockservice Require Import lockservice_nocrash nondet.

Section common_proof.
Context `{!heapGS Σ}.

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
     RET #(); ⌜((uint.Z v) + 1 = uint.Z (word.add v 1))%Z⌝
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
    assert (uint.Z (word.add v 1) >= uint.Z v)%Z by lia.
    destruct (bool_decide ((uint.Z v) + 1 < 2 ^ 64 ))%Z eqn:Hnov.
    {
      apply bool_decide_eq_true in Hnov.
      word.
    }
    apply bool_decide_eq_false in Hnov.
    assert (uint.Z v + (uint.Z 1) >= 2 ^ 64)%Z.
    { replace (uint.Z 1)%Z with (1)%Z by word. lia. }
    apply sum_overflow_check in H0.
    contradiction.
  }
Qed.

End common_proof.
