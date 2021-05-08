From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.single Require Import replica_proof.
From Goose.github_com.mit_pdos.gokv.paxi Require Import single.

Section single_proof.

Context `{!heapG Σ}.

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
  ∃ (promisePN valPN:u64) (v:u64),
  "HpromisedPN" ∷ r ↦[Replica :: "promisedPN"] #promisePN ∗
  "HvalPN" ∷ r ↦[Replica :: "valPN"] #valPN ∗
  "HacceptedVal" ∷ r ↦[Replica :: "acceptedVal"] #v ∗
  "HcommittedVal" ∷ r ↦[Replica :: "committedVal"] #v ∗
  "#Hacc_prop" ∷ pn_ptsto f γ (int.nat valPN) v ∗
  "#Hrej" ∷ (∀ pn', ⌜(int.nat valPN) < pn'⌝ → ⌜pn' ≤ int.nat promisePN⌝ → rejected γ pid pn') ∗
  "Hundec" ∷ ([∗ set] pn' ∈ (fin_to_set (C:=gset u64) u64), ⌜int.nat pn' ≤ int.nat promisePN⌝ ∨ undecided γ pid (int.nat pn')) ∗
  "Hvotes" ∷ True
  (* "Hpeers" ∷ *)
.

Lemma wp_PrepareRPC (r:loc) γ pid (reply_ptr:loc) (pn:u64) dummy_rep :
  {{{
       own_Replica r pid γ ∗
       own_PrepareReply reply_ptr dummy_rep
  }}}
    Replica__PrepareRPC #r #pn #reply_ptr
  {{{
       reply, RET #(); own_Replica r pid γ ∗
            own_PrepareReply reply_ptr reply ∗
            (⌜reply.(Prep_Success) = false⌝ ∨
             pn_ptsto f γ (int.nat reply.(Prep_Pn)) (reply.(Prep_Val)) ∗
             (∀ pn', ⌜pn' < int.nat pn⌝ → ⌜int.nat reply.(Prep_Pn) < pn'⌝ → rejected γ pid pn')
             )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_pures.
  iDestruct "Hpre" as "[Hown Hrep]".
  iNamed "Hown".

  wp_loadField.
  wp_if_destruct.
  { (* able to make a promise for that key *)
    wp_storeField.
    wp_loadField.
    iNamed "Hrep".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_storeField.
    iApply "HΦ".
    (* XXX: will be annoying to do a ghost update to a range of pns in "Hundec" *)
    admit.
  }
  { (* can't vote for caller *)
    iNamed "Hrep".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    iApply "HΦ".
    iSplitR "HPn HVal HSuccess".
    {
      iExists _, _, _.
      iFrame "∗#".
    }
    iSplitR "".
    {
      instantiate (1:=(mkPrepareReplyC _ _ _)).
      iFrame.
    }
    simpl.
    by iLeft.
  }
Admitted.

End single_proof.
