From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv.paxi Require Import single.
From Perennial.program_proof.single Require Import single_proof replica_proof.

Section try_decide_proof.

Context `{!heapG Σ}.
Context `{paxosG Σ u64}.

Context `{f:nat}.

Lemma wp_Clerk__Prepare ck pid γ reply_ptr dummy_rep (pn:u64) :
  (* is_Clerk r pid γ -∗ *)
  {{{
       own_PrepareReply reply_ptr dummy_rep
  }}}
    Clerk__Prepare #ck #pn #reply_ptr
  {{{
       reply, RET #();
            own_PrepareReply reply_ptr reply ∗
            (⌜reply.(Prep_Success) = false⌝ ∨
             pn_ptsto f γ (int.nat reply.(Prep_Pn)) (reply.(Prep_Val)) ∗
             (∀ pn', ⌜pn' < int.nat pn⌝ → ⌜int.nat reply.(Prep_Pn) < pn'⌝ → rejected γ pid pn')
             )
  }}}.
Proof.
Admitted.

Lemma wp_Clerk__Propose ck pid γ (pn:u64) (val:u64) :
  (* is_Clerk r pid γ -∗ *)
  {{{
       pn_ptsto f γ (int.nat pn) val
  }}}
    Clerk__Propose #ck #pn #val
  {{{
       (ret:bool), RET #ret;
       ⌜ret = false⌝ ∨ accepted γ pid (int.nat pn)
  }}}.
Proof.
Admitted.


Lemma wp_TryDecide s pid γ (v:u64) (outv_ptr:loc) :
  is_Replica s pid γ (f:=f) -∗
  {{{
       True
  }}}
    Replica__TryDecide #s #v #outv_ptr
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros "#His !#" (Φ) "Hpre HΦ".
  wp_lam.
  wp_pures.
  iNamed "His".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  wp_loadField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "Hmu_inv Hlocked".
    iNext.
    iExists _, _, _, _.
    iFrame "∗#".
  }
  wp_pures.

  wp_apply (typed_mem.wp_AllocAt uint64T).
  { naive_solver. }
  iIntros (numPrepared) "HnumPrepared".
  wp_pures.
  wp_store.

  wp_apply (typed_mem.wp_AllocAt uint64T).
  { naive_solver. }
  iIntros (highestPN) "HhighestPN".
  wp_pures.
  wp_store.

  wp_apply (typed_mem.wp_AllocAt uint64T).
  { naive_solver. }
  iIntros (highestVal) "HhighestVal".
  wp_pures.
  wp_store.

  wp_apply (wp_new_free_lock).
  iIntros (l) "Hl".
  wp_pures.
  (* Need to have read-only ownership of clerks for peers *)
