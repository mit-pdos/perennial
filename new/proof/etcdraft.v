From New.proof Require Import grove_prelude.
From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import sync.

Section proof.

Context `{!heapGS Σ}.

Lemma wp_newNetworkWithConfigInit (peers : list val) peers_sl :
  {{{
        own_slice peers_sl stateMachine (DfracOwn 1) peers
  }}}
    newNetworkWithConfigInit go_nil (slice.val peers_sl)
  {{{
        (nw : loc), RET #nw; True
  }}}
.
Proof.
Admitted.


Lemma wp_entsWithConfig terms_sl terms :
  {{{
        own_slice terms_sl uint64T (DfracOwn 1) terms
  }}}
    entsWithConfig go_nil (slice.val terms_sl)
  {{{ (r : loc), RET #r; True }}}
.
Proof.
Admitted.

Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_alloc preVote as "?".
  wp_alloc t_ptr as "?".
  wp_alloc cfg as "Hcfg".
  wp_alloc candState as "HcandState".
  wp_pures.
  wp_store.
  wp_pures.
  wp_alloc candTerm as "HcandTerm".
  wp_store.
  wp_load.
  wp_pures.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  wp_store.
  wp_alloc tests as "Htests".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  replace (zero_val funcT) with (zero_val' funcT).
  2:{ by rewrite zero_val_eq. }
  simpl.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw1".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw2".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_load.
  wp_load.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw3".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_load.
  wp_load.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw4".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw5".

  wp_pures.
  wp_load.
  wp_pures.

  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw6".
  wp_pures.
  wp_apply wp_slice_literal.
  { solve_has_go_type. }
  iIntros (?) "?".
Admitted.

End proof.
