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
  "#HdistinctPeers" ∷ □(|==> ∃ γtok, [∗ list] pid ∈ pids, pid ↪[γtok] ()) ∗
  "%HpeersLength" ∷ ⌜length peers = (2 * f + 1)%nat⌝ ∗
  "#HpidsValid" ∷ [∗ list] pid ∈ pids, ⌜pid < 2 * f + 1⌝
.

Notation "'[∗' 'range]' n1 < x < n2 , P" := ([∗ set] x ∈ (fin_to_set u64),
                                                   ⌜int.nat x ≤ int.nat n1⌝ ∨
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
                  ([∗ range] highestPn < pn' < pn, rejected γ pid (int.nat pn'))) ∗
  "%Hvalid" ∷ ⌜is_valid f S⌝
                  (* ([∗ set] pn' ∈ (fin_to_set u64),
      ⌜int.nat pn' ≤ int.nat highestPn⌝ ∨ ⌜int.nat pn ≤ int.nat pn'⌝ ∨
      (rejected γ pid (int.nat pn)))) *)
.

Definition propose_lock_inv γ γtok (pn:u64) (numAccepted_ptr:loc) : iProp Σ :=
  ∃ (numAccepted:u64) (S:gset nat),
  "HnumAccepted" ∷ numAccepted_ptr ↦[uint64T] #numAccepted ∗
  "%HacceptedSize" ∷ ⌜size S = int.nat numAccepted⌝ ∗
  "Htoks" ∷ ([∗ set] pid ∈ S, pid ↪[γtok] ()) ∗
  "#Haccepted" ∷ ([∗ set] pid ∈ S, accepted γ pid (int.nat pn)) ∗
  "%Hvalid" ∷ ⌜is_valid f S⌝
.

Lemma wp_TryDecide s pid γ (v:u64) (dummy_v:u64) (outv_ptr:loc) :
  is_Replica s pid γ (f:=f) -∗
  {{{
       outv_ptr ↦[uint64T] #dummy_v
  }}}
    Replica__TryDecide #s #v #outv_ptr
  {{{
       (b:bool), RET #b;
       ⌜b = true⌝ ∗ outv_ptr ↦[uint64T] #dummy_v ∨
       ∃ (outv:u64), outv_ptr ↦[uint64T] #outv ∗ cmd_is f γ outv
  }}}.
Proof.
  iIntros "#His !#" (Φ) "Houtv HΦ".
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
  wp_apply (release_spec with "[-HΦ Houtv]").
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

  set (pn:=(word.add promisePN 1)) in *.
  iAssert (peers_prop γ peers) with "[]" as (pids) "HpeersProp".
  { admit. } (* FIXME: this should be part of is_Replica *)
  iNamed "HpeersProp".
  iAssert (_) with "HdistinctPeers" as "#HdistinctPeersOne".
  iMod ("HdistinctPeersOne") as (γtok) "Hγtoks".
  (* FIXME: this should not disappear *)

  iMod (alloc_lock mutexN _ _ (prepare_lock_inv γ γtok pn numPrepared_ptr highestVal_ptr highestPN_ptr) with "Hl [HnumPrepared HhighestPN HhighestVal]") as "#Hl_inv".
  {
    iNext.
    iExists _, _, _, ∅.
    iFrame "∗#".
    iSplitL ""; first done.
    iSplitL "".
    { iApply (big_sepS_empty). done. }
    iSplitL ""; first admit. (* TODO: initial proposal *)
    iSplitL "".
    { by iApply (big_sepS_empty). }
    done.
  }

  wp_loadField.
  iMod (readonly_load with "HpeersSl") as (peersq) "HH".
  iDestruct (is_slice_small_sz with "HH") as %HpeersSz.

  wp_apply (typed_slice.wp_forSlice (V:=loc) (λ i, [∗ list] k ↦ pid ∈ pids, ⌜k < int.nat i⌝ ∨ pid ↪[γtok] ()
                        )%I with "[] [$HH Hγtoks]").
  {
    iIntros.
    clear Φ.
    iIntros (Φ) "!# [Hpre [%HindexLe %Hlookup]] HΦ".
    wp_pures.
    iDestruct (big_sepL2_length with "Hclerks") as %HlengthEq.
    iDestruct (big_sepL2_lookup_1_some with "Hclerks") as %Heq.
    { done. }
    destruct Heq as [pid' HpidLookup].
    iDestruct (big_sepL_lookup_acc_impl (int.nat i) with "Hpre") as "[Hγtok Hγtoks]".
    { naive_solver. }
    iDestruct "Hγtok" as "[%Hbad|Hγtok]".
    { exfalso. word. }
    wp_apply (wp_fork with "[Hγtok]").
    {
      iNext.
      wp_apply (wp_allocStruct).
      { naive_solver. }
      iIntros (reply_ptr) "Hreply".
      wp_pures.
      iDestruct (big_sepL2_lookup with "Hclerks") as "Hclerk".
      { done. }
      { done. }
      wp_apply (wp_Clerk__Prepare with "Hclerk [Hreply]").
      {
        instantiate (1:=(mkPrepareReplyC _ _ _)).
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        iFrame.
      }
      iIntros (reply) "[Hreply Hpost]".
      wp_pures.
      wp_pures.
      iNamed "Hreply".
      wp_loadField.
      wp_if_destruct.
      { (* got a promise *)
        iDestruct "Hpost" as "[%Hbad|#Hpost]".
        { exfalso. done. }
        wp_apply (acquire_spec with "Hl_inv").
        iIntros "[Hlocked Hown]".
        iNamed "Hown".
        wp_pures.
        wp_load.
        wp_store.
        wp_load.
        wp_loadField.
        wp_if_destruct.
        { (* new highest PN; need to update Hrejected *)
          wp_loadField.
          wp_store.
          wp_loadField.
          wp_store.
          wp_pures.
          wp_apply (release_spec with "[-]"); last done.
          {
            iFrame "Hl_inv Hlocked".
            iNext.
            iDestruct "Hpost" as "[Hptsto HrejectedPost]".
            iExists _, _, _, ({[ pid' ]} ∪ S).
            iFrame "∗#".
            assert (pid' ∈ S ∨ pid' ∉ S) as [Hbad|HnewPid'].
            {
              destruct (bool_decide (pid' ∈ S)) as [] eqn:X.
              { apply bool_decide_eq_true in X. naive_solver. }
              { apply bool_decide_eq_false in X. naive_solver. }
            }
            { (* impossible *)
              iDestruct (big_sepS_elem_of _ _ pid' with "Htoks") as "Htok".
              { done. }
              iExFalso.
              iDestruct (ghost_map_elem_valid_2 with "Hγtok Htok") as %[Hbad2 _].
              exfalso.
              naive_solver.
            }
            iSplitL "".
            {
              rewrite size_union.
              {
                iPureIntro.
                rewrite size_singleton.
                rewrite HpreparedSize.
                admit.
                (* TODO: numPrepared overflow guard *)
              }
              { set_solver. }
            }
            iSplitL "Hγtok Htoks".
            {
              iApply (big_sepS_insert with "[$Htoks $Hγtok]").
              done.
            }
            iSplitL "".
            { (* rejected *) (* TODO: these are generic "range" related lemmas *)
              iApply (big_sepS_insert with "[Hrejected]").
              { done. }
              iSplitL ""; last first.
              {
                iApply (big_sepS_impl with "Hrejected").
                iModIntro.
                iIntros.
                iApply (big_sepS_impl with "[$]").
                iModIntro.
                iIntros (y?) "[%HleHighestPn|$]".
                iLeft.
                iPureIntro.
                word.
              }
              {
                iApply (big_sepS_intro).
                iModIntro.
                iIntros (y?).
                assert (int.nat y ≤ int.nat reply.(Prep_Pn) ∨
                        int.nat reply.(Prep_Pn) < int.nat y) as [Hdone|Hineq] by word.
                { iLeft. done. }
                assert (int.nat pn ≤ int.nat y ∨
                        int.nat y < int.nat pn) as [Hdone|Hineq2] by word.
                { iRight; iLeft. done. }
                iRight; iRight.
                iApply "HrejectedPost".
                {
                  replace (word.add promisePN 1%Z) with (pn) by done.
                  iPureIntro.
                  word.
                }
                {
                  iPureIntro.
                  word.
                }
              }
            }
            { (* show that pid is less than 2f + 1 *)
              unfold is_valid in *.
              iIntros (q?).
              assert (q = pid' ∨ q ∈ S) as [Hcase|Hcase] by set_solver.
              {
                rewrite Hcase.
                iApply (big_sepL_lookup with "HpidsValid").
                done.
              }
              {
                iPureIntro.
                by apply Hvalid.
              }
            }
          }
        }
        { (* not a higher PN; just use Hpost to update Hrejected *)
          wp_pures.
          wp_apply (release_spec with "[-]").
          {
            iFrame "Hl_inv Hlocked".
            iNext.
            iExists _, _, _, ({[ pid' ]} ∪ S).
            iFrame "∗#".
            assert (pid' ∈ S ∨ pid' ∉ S) as [Hbad|HnewPid'].
            {
              destruct (bool_decide (pid' ∈ S)) as [] eqn:X.
              { apply bool_decide_eq_true in X. naive_solver. }
              { apply bool_decide_eq_false in X. naive_solver. }
            }
            { (* impossible *)
              iDestruct (big_sepS_elem_of _ _ pid' with "Htoks") as "Htok".
              { done. }
              iExFalso.
              iDestruct (ghost_map_elem_valid_2 with "Hγtok Htok") as %[Hbad2 _].
              exfalso.
              naive_solver.
            }
            iSplitL "".
            {
              rewrite size_union.
              {
                iPureIntro.
                rewrite size_singleton.
                rewrite HpreparedSize.
                admit.
                (* TODO: numPrepared overflow guard *)
              }
              { set_solver. }
            }
            iSplitL "Hγtok Htoks".
            {
              iApply (big_sepS_insert with "[$Htoks $Hγtok]").
              done.
            }
            iSplitL "".
            { (* rejected *)
              iApply (big_sepS_insert with "[$Hrejected]").
              { done. }
              iApply (big_sepS_intro).
              iModIntro.
              iIntros (y?).
              assert (int.nat y ≤ int.nat highestPn ∨
                      int.nat highestPn < int.nat y) as [Hdone|Hineq] by word.
              { iLeft. done. }
              assert (int.nat pn ≤ int.nat y ∨
                      int.nat y < int.nat pn) as [Hdone|Hineq2] by word.
              { iRight; iLeft. done. }
              iRight; iRight.
              iDestruct "Hpost" as "[_ Hpost]".
              iApply "Hpost".
              {
                replace (word.add promisePN 1%Z) with (pn) by done.
                iPureIntro.
                word.
              }
              {
                iPureIntro.
                word.
              }
            }
            { (* show that pid is less than 2f + 1 *)
              unfold is_valid in *.
              iIntros (q?).
              assert (q = pid' ∨ q ∈ S) as [Hcase|Hcase] by set_solver.
              {
                rewrite Hcase.
                iApply (big_sepL_lookup with "HpidsValid").
                done.
              }
              {
                iPureIntro.
                by apply Hvalid.
              }
            }
          }
          done.
        }
      }
      done.
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
  } (* end of first for loop *)
  {
    iApply (big_sepL_impl with "Hγtoks").
    iModIntro. iIntros.
    iRight.
    iFrame.
  }

  iIntros "_".
  wp_pures.
  wp_apply (acquire_spec with "Hl_inv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply (release_spec with "[$Hl_inv $Hlocked HnumPrepared HhighestPn HhighestVal Htoks]").
  { iNext. iExists _, _, _, _. iFrame "∗#". done. }
  wp_pures.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_if_destruct.
  { (* Got enough promises *)
    wp_pures.
    iAssert (pn_undec γ (int.nat pn)) with "[]" as "Hunproposed"; first admit. (* TODO: use majority election *)
    iMod (key_fact2 with "Hunproposed Hhighest_ptsto []") as "#Hptsto".
    {
      iModIntro.
      iIntros (???) "#Hcommitted".
      iDestruct (big_sepS_sepS with "Hrejected") as "Hrejected2".
      iDestruct (big_sepS_elem_of _ _ (U64 pn'') with "Hrejected2") as "Hrejected3".
      { set_solver. }
      iAssert ([∗ set] x ∈ S, rejected γ x (int.nat pn''))%I with "[Hrejected3]" as "HmajorityRejected".
      {
        iApply (big_sepS_impl with "Hrejected3").
        iModIntro. iIntros (??) "[%Hbad|[%Hbad|$]]".
        {
          exfalso.
          assert (int.nat highestPn < int.nat pn'') by word.
          word.
        }
        {
          exfalso.
          assert (int.nat pn'' < int.nat pn) by word.
          word.
        }
      }
      iNamed "Hcommitted".
      iDestruct "Hcommitted" as "[_ [%Hmaj HmajorityAccepted]]".
      unfold is_majority in Hmaj.
      (* TODO: need to have is_valid f S to establish is_majority f S *)
      admit.
    }

    (* Do the same thing as before to deal with the loop *)
    wp_apply (wp_new_free_lock).
    iIntros (l2) "Hl2".
    wp_pures.
    wp_apply (typed_mem.wp_AllocAt).
    { naive_solver. }
    iIntros (numAccepted_ptr) "HnumAccepted".
    wp_pures.
    wp_store.

    iAssert (_) with "HdistinctPeers" as "#HdistinctPeersOne".
    iClear "Hl_inv".
    clear γtok.
    iMod ("HdistinctPeersOne") as (γtok) "Hγtoks".
    (* FIXME: this should not disappear *)

    iMod (alloc_lock mutexN _ _ (propose_lock_inv γ γtok pn numAccepted_ptr) with "Hl2 [HnumAccepted]") as "#Hl2_inv".
    {
      iNext. iExists _, ∅.
      iFrame "∗#".
      iSplitL ""; first done.
      iSplitL ""; first by iApply (big_sepS_empty).
      iSplitL ""; first by iApply (big_sepS_empty).
      done.
    }

    (* Prepare to do for loop *)
    clear peersq.
    iMod (readonly_load with "HpeersSl") as (peersq) "HH".

    iClear "Hrejected".
    clear Hvalid HpreparedSize S.
    wp_loadField.
    wp_apply (typed_slice.wp_forSlice (V:=loc) (λ i, [∗ list] k ↦ pid ∈ pids, ⌜k < int.nat i⌝ ∨ pid ↪[γtok] ()
                          )%I with "[] [$HH Hγtoks]").
    {
      clear Φ.
      iIntros (???Φ) "!# [Hpre [%HindexLe %HpeersLookup]] HΦ".
      wp_pures.

      iDestruct (big_sepL2_length with "Hclerks") as %HlengthEq.
      iDestruct (big_sepL2_lookup_1_some with "Hclerks") as %Heq.
      { done. }
      destruct Heq as [pid' HpidLookup].
      iDestruct (big_sepL_lookup_acc_impl (int.nat i) with "Hpre") as "[Hγtok Hγtoks]".
      { naive_solver. }
      iDestruct "Hγtok" as "[%Hbad|Hγtok]".
      { exfalso. word. }

      wp_apply (wp_fork with "[Hγtok]").
      {
        iNext.
        replace (word.add promisePN 1%Z) with (pn) by done.

        iDestruct (big_sepL2_lookup with "Hclerks") as "Hclerk".
        { done. }
        { done. }
        wp_apply (wp_Clerk__Propose with "Hclerk [$Hptsto]").
        iIntros (ret) "Hret".
        wp_pures.
        wp_if_destruct.
        { (* accepted *)
          iDestruct "Hret" as "[%Hbad|#HacceptedReply]"; first by exfalso.
          wp_apply (acquire_spec with "Hl2_inv").
          iIntros "[Hlocked Hown]".
          iRename "Haccepted" into "HacceptedServer".
          iNamed "Hown".
          wp_pures.
          wp_load.
          wp_store.
          wp_apply (release_spec with "[$Hl2_inv $Hlocked HnumAccepted Hγtok Htoks]"); last done.
          {
            iNext.
            iExists _, ({[pid']} ∪ S).
            iFrame "∗#".

            assert (pid' ∈ S ∨ pid' ∉ S) as [Hbad|HnewPid'].
            {
              destruct (bool_decide (pid' ∈ S)) as [] eqn:X.
              { apply bool_decide_eq_true in X. naive_solver. }
              { apply bool_decide_eq_false in X. naive_solver. }
            }
            { (* impossible *)
              iDestruct (big_sepS_elem_of _ _ pid' with "Htoks") as "Htok".
              { done. }
              iExFalso.
              iDestruct (ghost_map_elem_valid_2 with "Hγtok Htok") as %[Hbad2 _].
              exfalso.
              naive_solver.
            }

            iSplitL "".
            {
              admit. (* TODO: overflow *)
            }
            iSplitL "Hγtok Htoks".
            {
              iApply (big_sepS_insert with "[$Htoks $Hγtok]").
              done.
            }
            iSplitL "".
            {
              iApply (big_sepS_insert with "[$Haccepted $HacceptedReply]").
              done.
            }
            { (* show that pid is less than 2f + 1 *)
              unfold is_valid in *.
              iIntros (q?).
              assert (q = pid' ∨ q ∈ S) as [Hcase|Hcase] by set_solver.
              {
                rewrite Hcase.
                iApply (big_sepL_lookup with "HpidsValid").
                done.
              }
              {
                iPureIntro.
                by apply Hvalid.
              }
            }
          }
        }
        {
          done.
        }
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
    wp_pures.

    wp_apply (acquire_spec with "Hl2_inv").
    iIntros "[Hlocked Hown]".
    iRename "Haccepted" into "HacceptedOld".
    iNamed "Hown".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (release_spec with "[-HΦ Houtv]").
    { iFrame "Hl2_inv Hlocked". iNext; iExists _, _; iFrame "∗#"; done. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_pures.
    wp_if_destruct.
    {
      wp_store.
      iApply "HΦ".
      iRight.
      iExists highestVal.
      iFrame.
      iMod (key_fact1 f mutexN γ (int.nat pn) highestVal with "[] Hptsto [Haccepted]").
      { admit. } (* FIXME: add this invariant somewhere *)
      {
        iExists S.
        iSplitL "".
        {
          iExists _.
          iDestruct "Hptsto" as "[$ _]".
        }
        iFrame "Haccepted".
        iPureIntro.
        split; first done.
        rewrite HacceptedSize.
        (* TODO: Pure reasoning to know that numAccepted > f+1 *)
        admit.
      }
      iFrame "#∗".
      done.
    }
    iApply "HΦ".
    iModIntro.
    iLeft. iFrame.
    done.
  }
  {
    iApply "HΦ".
    iModIntro.
    iLeft. iFrame.
    done.
  }
Admitted.

End try_decide_proof.
