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

Definition is_Clerk (γ:single_names) (r:loc) (pid:nat) : iProp Σ.
Admitted.

Instance is_Clerk_pers r pid γ : Persistent (is_Clerk r pid γ).
Admitted.

Lemma wp_Clerk__Prepare ck pid γ reply_ptr dummy_rep (pn:u64) :
  is_Clerk γ ck pid -∗
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
  is_Clerk γ ck pid -∗
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

Context `{!ghost_mapG Σ nat unit}.

Definition peers_prop γ (peers:list loc) : iProp Σ :=
  ∃ (pids:list nat),
  "#Hclerks" ∷ ([∗ list] ck;pid ∈ peers; pids, (is_Clerk γ ck pid)) ∗
  "#HdistinctPeers" ∷ □(|==> ∃ γtok, [∗ list] pid ∈ pids, pid ↪[γtok] ())
.

Notation "'[∗' 'range]' n1 < x < n2 , P" := ([∗ set] x ∈ (fin_to_set u64),
                                                   ⌜int.nat n1 ≤ int.nat x⌝ ∨
                                           ⌜int.nat n2 ≤ int.nat x⌝ ∨
                                           ((λ x, P) x))%I
  (at level 200, n1 at level 10, n2 at level 10, x at level 1, right associativity,
   format "[∗ range]  n1 < x < n2 ,  P") : bi_scope.

Definition prepare_lock_inv γ γtok (pn:u64) (numPrepared_ptr highestVal_ptr highestPn_ptr:loc) : iProp Σ :=
  ∃ (numPrepared highestPn:u64) (highestVal:u64) (S:gset nat),
  "HnumPrepared" ∷ numPrepared_ptr ↦[uint64T] #numPrepared ∗
  "HhighestPn" ∷ highestPn_ptr ↦[uint64T] #highestPn ∗
  "HhighestVal" ∷ highestVal_ptr ↦[uint64T] #highestVal ∗
  "%HpreparedSize" ∷ ⌜size S = int.nat numPrepared⌝ ∗
  "Htoks" ∷ ([∗ set] pid ∈ S, pid ↪[γtok] ()) ∗
  "#Hhighest_ptsto" ∷ pn_ptsto f γ (int.nat highestPn) highestVal ∗
  "#Hrejected" ∷ ([∗ set] pid ∈ S,
                  ([∗ range] highestPn < pn' < pn, rejected γ pid (int.nat pn')))
                  (* ([∗ set] pn' ∈ (fin_to_set u64),
      ⌜int.nat pn' ≤ int.nat highestPn⌝ ∨ ⌜int.nat pn ≤ int.nat pn'⌝ ∨
      (rejected γ pid (int.nat pn)))) *)
.

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
  iIntros (numPrepared_ptr) "HnumPrepared".
  wp_pures.
  wp_store.

  wp_apply (typed_mem.wp_AllocAt uint64T).
  { naive_solver. }
  iIntros (highestPN_ptr) "HhighestPN".
  wp_pures.
  wp_store.

  wp_apply (typed_mem.wp_AllocAt uint64T).
  { naive_solver. }
  iIntros (highestVal_ptr) "HhighestVal".
  wp_pures.
  wp_store.

  wp_apply (wp_new_free_lock).
  iIntros (l) "Hl".
  wp_pures.

  set (pn:=(word.add promisePN 1)).
  iAssert (peers_prop γ peers) with "[]" as (pids) "HpeersProp".
  { admit. } (* FIXME: this should be part of is_Replica *)
  iNamed "HpeersProp".
  iMod ("HdistinctPeers") as (γtok) "Hγtoks".
  (* FIXME: this should not disappear *)

  iMod (alloc_lock mutexN _ _ (prepare_lock_inv γ γtok pn numPrepared_ptr highestVal_ptr highestPN_ptr) with "Hl [HnumPrepared HhighestPN HhighestVal]").
  {
    iNext.
    iExists _, _, _, ∅.
    iFrame "∗#".
    iSplitL ""; first done.
    iSplitL "".
    { iApply (big_sepS_empty). done. }
    iSplitL ""; first admit. (* TODO: initial proposal *)
    iApply (big_sepS_empty).
    done.
  }

  wp_loadField.
  iMod (readonly_load with "HpeersSl") as (peersq) "HH".
  iDestruct (is_slice_small_sz with "HH") as %HpeersSz.

  Search "wp_alloc".
  Search struct.ptrT.
  wp_apply (typed_slice.wp_forSlice (V:=loc) (λ i, [∗ list] k ↦ pid ∈ pids, ⌜k < int.nat i⌝ ∨ pid ↪[γtok] ()
                        )%I with "[] [$HH Hγtoks]").
  {
    iIntros.
    clear Φ.
    iIntros (Φ) "!# [Hpre [%HindexLe %Hlookup]] HΦ".
    wp_pures.
    iDestruct (big_sepL2_length with "Hclerks") as %HlengthEq.
    assert (∃ ck, peers !! (int.nat i) = Some ck) as [ck Htemp].
    {
      apply list_lookup_lt.
      rewrite -typed_slice.list_untype_length.
      word.
    }
    iDestruct (big_sepL2_lookup_1_some with "Hclerks") as %Heq.
    { done. }
    destruct Heq as [pid' HpidLookup].
    iDestruct (big_sepL_lookup_acc_impl (int.nat i) with "Hpre") as "[Hγtok Hγtoks]".
    { naive_solver. }
    iDestruct "Hγtok" as "[%Hbad|Hγtok]".
    { exfalso. word. }
    wp_apply (wp_fork with "[Hγtok]").
    {
      admit. (* FIXME: Will need per-thread token for updating state under mutex l *)
      (* Will make (I n) be ownership of all of the tokens except for the first n (exclusive) *)
    }
    iApply "HΦ".
    iApply "Hγtoks".
    {
      iModIntro.
      iIntros (????) "[%Hcase|$]".
      iLeft; iPureIntro.
      word.
    }
    iLeft.
    iPureIntro.
    clear -i HindexLe.
    word. (* XXX: Because int.Z i < int.Z blah -> int.Z i < 2^64 - 1 *)
  }
  {
    iApply (big_sepL_impl with "Hγtoks").
    iModIntro. iIntros.
    iRight.
    iFrame.
  }

  iIntros "_".

Admitted.


End try_decide_proof.
