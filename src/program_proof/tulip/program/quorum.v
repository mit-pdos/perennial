From Perennial.program_proof.tulip Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import quorum.

Section cquorum.
  Context `{!heapGS Σ}.

  Theorem wp_ClassicQuorum (n : u64) :
    {{{ True }}}
      ClassicQuorum #n
    {{{ (x : u64), RET #x; ⌜uint.Z x = (uint.Z n / 2 + 1)%Z⌝ }}}.
  Proof.
    (*@ func ClassicQuorum(n uint64) uint64 {                                   @*)
    (*@     // floor(n / 2) + 1                                                 @*)
    (*@     return n / 2 + 1                                                    @*)
    (*@ }                                                                       @*)
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    iApply "HΦ".
    iPureIntro. word.
  Qed.

End cquorum.
