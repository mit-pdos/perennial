(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import examples.
From Perennial.program_proof.mvcc Require Import mvcc_ghost txn_proof.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_Example1 (txn : loc) γ :
  {{{ is_txn_uninit txn γ }}}
    Example1 #txn
  {{{ (total : u64), RET #total; ⌜(int.Z total) = 10⌝ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  wp_call.
  wp_apply (wp_txn__Begin with "Htxn").
  iIntros "Htxn".
  wp_pures.
  (* Read key 0 *)
  wp_apply (wp_txn__Get with "Htxn").
  iIntros (v ok) "Hget".
  unfold spec_get.
  rewrite lookup_empty.
  iDestruct "Hget" as (v0) "[Htxn <-]".
  wp_pures.
  (* Read key 2 *)
  wp_apply (wp_txn__Get with "Htxn").
  iIntros (v' ok') "Hget".
  unfold spec_get.
  rewrite lookup_empty.
  Set Printing Coercions.
  replace (<[(U64 0):=_]> _ !! (U64 2)) with (None : option dbval); last first.
  { symmetry. by rewrite lookup_insert_None. }
  iDestruct "Hget" as (v2) "[Htxn <-]".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iDestruct (db_consistent with "Htxn") as (dbmap) "%Hdbmap".
  iPureIntro.
  destruct Hdbmap as [(v0' & v2' & (Hv0' & Hv2' & HC)) Hsubset].
  (*
  assert (Hv0 : dbmap !! (U64 0) = Some v0).
  { eapply lookup_weaken; last eauto.
    rewrite lookup_insert_ne; last done.
    apply lookup_insert.
  }
  assert (Hv2 : dbmap !! (U64 2) = Some v2).
  { eapply lookup_weaken; last eauto.
    apply lookup_insert.
  }
  rewrite Hv0 in Hv0'. inversion Hv0'.
  rewrite Hv2 in Hv2'. inversion Hv2'.
  subst.
  word.
  *)
Admitted.

End heap.
