From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.single Require Import replica_proof.
From Goose.github_com.mit_pdos.gokv.paxi Require Import single.

Section single_proof.

Context `{!heapGS Σ}.

Record PrepareReplyC := mkPrepareReplyC
{
    Prep_Pn : u64;
    Prep_Val : u64;
    Prep_Success : bool;
}
.
Definition own_PrepareReply (reply_ptr:loc) (reply:PrepareReplyC) : iProp Σ :=
  "HPn" ∷ reply_ptr ↦[PrepareReply :: "Pn"] #reply.(Prep_Pn) ∗
  "HVal" ∷ reply_ptr ↦[PrepareReply :: "Val"] #reply.(Prep_Val) ∗
  "HSuccess" ∷ reply_ptr ↦[PrepareReply :: "Success"] #reply.(Prep_Success)
.

(* TODO: do majority election ghost proof, to give winner of a proposal number
   ownership of the pn_undec *)

Context `{paxosG Σ u64}.
Context `{f:nat}.

Definition own_Replica (r:loc) (pid:nat) γ : iProp Σ :=
  ∃ (promisePN acceptedPN:u64) (v:u64) (cv:u64),
  "HpromisedPN" ∷ r ↦[Replica :: "promisedPN"] #promisePN ∗
  "HacceptedPN" ∷ r ↦[Replica :: "acceptedPN"] #acceptedPN ∗
  "HacceptedVal" ∷ r ↦[Replica :: "acceptedVal"] #v ∗
  "HcommittedVal" ∷ r ↦[Replica :: "committedVal"] #cv ∗
  "#Hacc_prop" ∷ pn_ptsto f γ (uint.nat acceptedPN) v ∗
  "#Hrej" ∷ (∀ pn', ⌜(uint.nat acceptedPN) < pn'⌝ → ⌜pn' ≤ uint.nat promisePN⌝ → rejected γ pid pn') ∗
  "Hundec" ∷ ([∗ set] pn' ∈ (fin_to_set (C:=gset u64) u64), ⌜uint.nat pn' < uint.nat promisePN⌝ ∨ ⌜uint.nat pn' ≤ uint.nat acceptedPN⌝ ∨ undecided γ pid (uint.nat pn')) ∗
  "#Haccepted" ∷ accepted γ pid (uint.nat acceptedPN) ∗
  "Hvotes" ∷ True
  (* "Hpeers" ∷ *)
.

Definition mutexN := nroot.@ "mutex".

Definition is_Replica (r:loc) pid γ : iProp Σ :=
  ∃ mu peers_sl (peers:list loc),
  "#Hmu" ∷ readonly (r ↦[Replica :: "mu"] mu) ∗
  "#Hmu_inv" ∷ is_lock mutexN mu (own_Replica r pid γ) ∗
  "#Hpeers" ∷ readonly (r ↦[Replica :: "peers"] (slice_val peers_sl)) ∗
  (* XXX: what does refT (struct.t ... ) vs struct.ptrT ... *)
  "#HpeersSl" ∷ readonly (typed_slice.own_slice_small peers_sl (refT (struct.t Clerk)) 1%Qp peers)
  (* "#HpeersAreClerks" *)
.

Lemma wp_PrepareRPC (r:loc) γ pid (reply_ptr:loc) (pn:u64) dummy_rep :
  is_Replica r pid γ -∗
  {{{
       own_PrepareReply reply_ptr dummy_rep
  }}}
    Replica__PrepareRPC #r #pn #reply_ptr
  {{{
       reply, RET #();
            own_PrepareReply reply_ptr reply ∗
            (⌜reply.(Prep_Success) = false⌝ ∨
             pn_ptsto f γ (uint.nat reply.(Prep_Pn)) (reply.(Prep_Val)) ∗
             (∀ pn', ⌜pn' < uint.nat pn⌝ → ⌜uint.nat reply.(Prep_Pn) < pn'⌝ → rejected γ pid pn')
             )
  }}}
.
Proof.
  iIntros "#His !#" (Φ) "Hpre HΦ".
  wp_rec.
  wp_pures.
  iNamed "His".

  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_loadField.
  wp_if_destruct.
  { (* able to make a promise for that key *)
    wp_storeField.
    wp_loadField.
    iNamed "Hpre".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_storeField.
    wp_loadField.
    iApply wp_fupd.
    (* assert (fin_to_set u64 = (rangeSet ) ∪ (fin_to_set u64)) as Hsplit.
    iDestruct (big_sepS_union with "Hundec") as "[Htorej Hundec]". *)

    (* XXX: will be annoying to do a ghost update to a range of pns in "Hundec" *)
    admit.
  }
  { (* can't vote for caller *)
    iNamed "Hpre".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[$Hmu_inv $Hlocked HpromisedPN HacceptedVal HacceptedPN Hundec Haccepted Hvotes HcommittedVal]").
    {
      iNext. iExists _, _, _, _.
      iFrame "∗#".
    }
    iApply "HΦ".
    iSplitR "".
    {
      instantiate (1:=(mkPrepareReplyC _ _ _)).
      iFrame.
    }
    simpl.
    by iLeft.
  }
Admitted.

Lemma wp_ProposeRPC (r:loc) γ pid (args_ptr reply_ptr:loc) (pn:u64) (val:u64) (dummy_rep:bool) :
  is_Replica r pid γ -∗
  {{{
       pn_ptsto f γ (uint.nat pn) val
  }}}
    Replica__ProposeRPC #r #pn #val
  {{{
       (ret:bool), RET #ret;
       ⌜ret = false⌝ ∨ accepted γ pid (uint.nat pn)
  }}}
.
Proof.
  iIntros "#His !#" (Φ) "#Hpre HΦ".
  wp_rec.
  wp_pures.
  iNamed "His".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_loadField.
  wp_pures.
  wp_bind (if: #(bool_decide (_)) then _ else #false)%E.
  wp_if_destruct.
  { (* *)
    wp_loadField.
    wp_if_destruct.
    { (* able to accept *)
      (* undecided ==∗ accepted *)
      assert (uint.nat acceptedPN = uint.nat pn ∨ uint.nat acceptedPN < uint.nat pn) as [HacceptedBefore|Hfresh] by word.
      { (* just send old accept witness *)
        assert (acceptedPN = pn) as -> by word.
        iDestruct (pn_ptsto_agree with "Hpre Hacc_prop") as %->.
        wp_storeField.
        wp_storeField.
        wp_loadField.
        wp_apply (release_spec with "[-HΦ]").
        {
          iFrame "Hmu_inv Hlocked".
          iNext.
          iExists _, _, _, _.
          iFrame "∗#".
        }
        wp_pures.
        iApply "HΦ"; iModIntro.
        iFrame "#".
      }
      iDestruct (big_sepS_elem_of_acc_impl pn with "Hundec") as "[Hundec1 Hundec]".
      { set_solver. }
      (* need to accept now *)
      iDestruct "Hundec1" as "[%Hbad|[%Hbad|Hundec1]]".
      { exfalso. lia. }
      { exfalso. lia. }
      (* TODO: now we can go undecided ==∗ accepted *)
      iMod (do_accept with "Hundec1") as "#HacceptedNew".
      wp_storeField.
      wp_storeField.
      wp_loadField.
      wp_apply (release_spec with "[-HΦ]").
      {
        iFrame "Hmu_inv Hlocked".
        iNext.
        iExists _, _, _, _.
        iFrame "HacceptedPN HacceptedVal ∗#".
        iSplitL "".
        { (* XXX: acceptedPN > promisePN now, so we don't need to keep any reject witnesses *)
          iIntros (pn' Hle1 Hle2).
          assert (uint.nat pn < uint.nat acceptedPN) as Hineq by word.
          iApply "Hrej".
          { word. }
          { word. }
        }
        iApply "Hundec".
        {
          iModIntro.
          iIntros (???) "Hcases".
          iDestruct "Hcases" as "[$|[%Hcase|$]]".
          iRight. iLeft.
          iPureIntro.
          word. (* because acceptedPN ≤ pn *)
        }
        iRight; iLeft; done.
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame "#".
    }
    (* won't accept because acceptedPN too high *)
    (* if we wanted, we could have it accept even if acceptedPN is too high, so
      long as we don't update our "highest accepted" state; we could e.g.
      automatically accept everything from promisePN up to acceptedPN all the
      time, and that would make accepting in this case trivial. *)
    admit. (* This is a copy of above; wp_and doesn't work well *)
  }
  {
    wp_pures.
    admit. (* same exact proof as above, though for a different reason *)
  }
Admitted.


End single_proof.
