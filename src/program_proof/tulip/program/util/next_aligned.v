From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof Require Import std_proof.
From Goose.github_com.mit_pdos.tulip Require Import util.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section next_aligned.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Lemma Z_next_aligned (c i l : Z) :
    0 ≤ l < i ->
    (c + (l - (c `mod` i))) `mod` i = l.
  Proof.
    intros Horder.
    rewrite Zplus_mod Zminus_mod Zmod_mod -Zminus_mod -Zplus_mod.
    replace (c + _) with l by lia.
    apply Zmod_small. lia.
  Qed.

  Theorem wp_NextAligned (current : u64) (interval : u64) (low : u64) :
    uint.Z interval < 2 ^ 63 ->
    0 ≤ uint.Z low < uint.Z interval ->
    {{{ True }}}
      NextAligned #current #interval #low
    {{{ (n : u64), RET #n;
        ⌜uint.Z current < uint.Z n ∧ uint.Z n `mod` uint.Z interval = uint.Z low⌝
    }}}.
  Proof.
    iIntros (Hitv Horder Φ) "_ HΦ".
    wp_rec. wp_pures.

    (*@ func NextAligned(current, interval, low uint64) uint64 {                @*)
    (*@     var delta uint64                                                    @*)
    (*@                                                                         @*)
    wp_apply (wp_ref_of_zero); first done.
    iIntros (deltaRef) "HdeltaRef".
    wp_pures.

    (*@     rem := current % interval                                           @*)
    (*@     if rem < low {                                                      @*)
    (*@         delta = low - rem                                               @*)
    (*@     } else {                                                            @*)
    (*@         delta = interval + low - rem                                    @*)
    (*@     }                                                                   @*)
    (*@     return std.SumAssumeNoOverflow(current, delta)                      @*)
    (*@ }                                                                       @*)
    set rem := (word.modu _ _).
    wp_if_destruct; wp_store; wp_load; wp_apply wp_SumAssumeNoOverflow.
    - iIntros (Hoverflow). iApply "HΦ". iPureIntro.
      rewrite Hoverflow.
      split; first word.
      rewrite word.unsigned_sub_nowrap; last lia.
      rewrite word.unsigned_modu_nowrap; last lia.
      apply Z_next_aligned.
      lia.
    - iIntros (Hoverflow). iApply "HΦ". iPureIntro.
      rewrite Hoverflow.
      rewrite word.unsigned_sub_nowrap; last first.
      { rewrite word.unsigned_add_nowrap; last lia.
        rewrite word.unsigned_modu_nowrap; lia.
      }
      rewrite word.unsigned_add_nowrap; last lia.
      rewrite word.unsigned_modu_nowrap; last lia.
      rewrite word.unsigned_modu_nowrap in Heqb; last lia.
      split; first lia.
      rewrite -Z.add_sub_assoc Z.add_assoc (Z.add_comm (uint.Z current)) -Z.add_assoc.
      rewrite Zplus_mod Z_mod_same_full Z.add_0_l Zmod_mod.
      apply Z_next_aligned.
      lia.
  Qed.

End next_aligned.
