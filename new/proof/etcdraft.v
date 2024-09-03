From New.proof Require Import grove_prelude.
From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import sync.

Section proof.

Context `{!heapGS Σ}.
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

  wp_alloc tests as "Htests".
  wp_pures.
  wp_load.
  wp_pures.
  (* FIXME: spec for slice.literal *)
Admitted.

End proof.
