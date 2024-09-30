From Perennial.program_proof.tulip Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import util.

Definition sorted_u64 (ns : list u64) :=
  ∀ i j x y, (i ≤ j)%nat -> ns !! i = Some x -> ns !! j = Some y -> uint.Z x ≤ uint.Z y.

Section sort.
  Context `{!heapGS Σ}.

  Theorem wp_Sort (nsP : Slice.t) (ns : list u64) :
    {{{ own_slice nsP uint64T (DfracOwn 1) ns }}}
      Sort (to_val nsP)
    {{{ (ns' : list u64), RET #(); 
        own_slice nsP uint64T (DfracOwn 1) ns' ∗ ⌜sorted_u64 ns' ∧ ns' ≡ₚ ns⌝
    }}}.
  Proof.
    (*@ func Sort(ns []uint64) {                                                @*)
    (*@     // NB: Follow the proof of wrbuf.sortEntsByKey                      @*)
    (*@     var i uint64 = 1                                                    @*)
    (*@     for i < uint64(len(ns)) {                                           @*)
    (*@         var j uint64 = i                                                @*)
    (*@         for j > 0 {                                                     @*)
    (*@             if ns[j - 1] <= ns[j] {                                     @*)
    (*@                 break                                                   @*)
    (*@             }                                                           @*)
    (*@             swap(ns, j - 1, j)                                          @*)
    (*@             j--                                                         @*)
    (*@         }                                                               @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

End sort.
