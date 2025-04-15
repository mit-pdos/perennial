From iris.base_logic.lib Require Import saved_prop.

From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.program_proof Require Import proof_prelude.

From Perennial.goose_lang.lib.channel Require Import auth_set.

Record chan_names :=
 {
    sender_name: gname;
    receiver_name: gname;
    close_name: gname;
 }.

Class closePropTrackerG Σ := ClosePropTrackerG {
    sender_main_saved_predG :: savedPredG Σ nat;
    close_prop_auth_setG :: auth_setG Σ gname;
  }.

Definition closePropTrackerΣ: gFunctors :=
  #[ savedPredΣ nat; auth_setΣ gname ].

#[global] Instance subG_closePropTrackerG Σ : subG closePropTrackerΣ Σ → closePropTrackerG Σ.
Proof. solve_inG. Qed.
    
Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section lemmas.
Context `{!ffi_interp ffi}.
Context `{!inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!closePropTrackerG Σ}.
Context `{heapGS Σ}.
Implicit Types (v:val). 

Definition own_chan_counter_frag 
(γ : gname) (n : nat) (q : Qp) : iProp Σ :=
   own γ (◯ Some (q, n)).

Local Definition own_chan_counter_auth
(γ : gname) (n : nat) (frozen : bool) : iProp Σ :=
own γ (●{if frozen then DfracDiscarded else (DfracOwn 1)} Some (1%Qp, n)).

Definition own_send_counter_frag (γ: chan_names) (n: nat) (q: Qp) : iProp Σ :=
    own_chan_counter_frag γ.(sender_name) n q.

Definition own_send_counter_auth (γ : chan_names) 
   (n : nat)  (frozen : bool) : iProp Σ :=
   own_chan_counter_auth γ.(sender_name) n frozen.

Definition own_recv_counter_frag (γ: chan_names) (n: nat) (q: Qp) : iProp Σ :=
   own_chan_counter_frag γ.(receiver_name) n q.

Definition own_recv_counter_auth (γ : chan_names) 
  (n : nat) (frozen : bool) : iProp Σ :=
  own_chan_counter_auth γ.(receiver_name) n frozen.

Lemma chan_counter_agree (γ: gname) (n: nat) (i: nat) :
 ∀ frozen,
  own_chan_counter_auth γ n frozen -∗ own_chan_counter_frag γ i 1 -∗ 
   ⌜i = n⌝.
  Proof.
    intro frozen.
    unfold own_chan_counter_auth, own_chan_counter_frag.
    iIntros "Hauth". iIntros "Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hin.
    iPureIntro.
    destruct frozen.
    {
      apply auth_both_dfrac_valid_discrete in Hin.
      destruct Hin as (H1 & H2 & H3).
      apply Some_included_exclusive in H2.
      {
        apply H2.
      }
      {
        apply _.
      }
      {
       done. 
      }
    }
    {
      apply auth_both_valid_discrete in Hin.
      destruct Hin as [Hin _].
      apply Some_included_exclusive in Hin. 
      {
        destruct Hin as [_ Hin]; cbn in Hin.
        apply leibniz_equiv in Hin.
        done.
      }
      { apply _. }
      { done. }
    }
  Qed.

Lemma chan_counter_update (γ: gname) (n: nat) (i: nat) (q : Qp) :
  (own_chan_counter_auth γ n false ∗ own_chan_counter_frag γ i q) ==∗ 
  (own_chan_counter_auth γ (S n) false ∗ own_chan_counter_frag γ (S i) q).
Proof.
    unfold own_chan_counter_auth, own_chan_counter_frag.
    iIntros "H".
    rewrite -!own_op.
    iApply (own_update with "H").
    apply auth_update.
    apply option_local_update.
    apply prod_local_update_2.
    apply (op_local_update_discrete _ _ 1).
    done.
  Qed.

Lemma chan_counter_split (γ : gname) (n m : nat) (p q : Qp) :
  own_chan_counter_frag γ (n + m) (p + q) ⊣⊢ own_chan_counter_frag γ n p ∗ own_chan_counter_frag γ m q.
Proof.
 setoid_rewrite <-own_op.
  iSplit.
  { iIntros "H". done. }
  { iIntros "H". done. }
Qed.

Lemma send_counter_agree (γ: chan_names) (n: nat) (i: nat) :
 ∀ frozen,
  own_send_counter_auth γ n frozen -∗ own_send_counter_frag γ i 1 -∗ 
   ⌜i = n⌝.
  Proof.
    apply chan_counter_agree.
  Qed.

Lemma send_counter_update (γ: chan_names) (n: nat) (i: nat) (q : Qp) :
  (own_send_counter_auth γ n false ∗ own_send_counter_frag γ i q) ==∗ 
  (own_send_counter_auth γ (S n) false ∗ own_send_counter_frag γ (S i) q).
Proof.
  apply chan_counter_update.
  Qed.

Lemma send_counter_split (γ : chan_names) (n m : nat) (p q : Qp) :
  own_send_counter_frag γ (n + m) (p + q) ⊣⊢ own_send_counter_frag γ n p ∗ own_send_counter_frag γ m q.
Proof.
  apply chan_counter_split.
Qed.

Lemma recv_counter_agree (γ: chan_names) (n: nat) (i: nat) :
 ∀ frozen,
  own_recv_counter_auth γ n frozen -∗ own_recv_counter_frag γ i 1 -∗ 
   ⌜i = n⌝.
  Proof.
    apply chan_counter_agree.
  Qed.

Lemma recv_counter_update (γ: chan_names) (n: nat) (i: nat) (q : Qp) :
  (own_recv_counter_auth γ n false ∗ own_recv_counter_frag γ i q) ==∗ 
  (own_recv_counter_auth γ (S n) false ∗ own_recv_counter_frag γ (S i) q).
Proof.
  apply chan_counter_update.
  Qed.

Lemma recv_counter_split (γ : chan_names) (n m : nat) (p q : Qp) :
  own_recv_counter_frag γ (n + m) (p + q) ⊣⊢ own_recv_counter_frag γ n p ∗ own_recv_counter_frag γ m q.
Proof.
  apply chan_counter_split.
Qed.

Definition own_closed_tok_frag (γ: chan_names) (γi: gname) (R:nat -> iProp Σ): iProp Σ :=
    auth_set_frag γ.(close_name) γi ∗ saved_pred_own γi (DfracDiscarded) R.

Definition own_closed_tok_auth (γ: chan_names) (R:nat -> iProp Σ): iProp Σ :=
  ∃ (close_tok_names: gset gname),
    "Hownauth" ∷ auth_set_auth γ.(close_name) close_tok_names ∗ 
  ∀ (n: nat),
   "HRcentral" ∷ (▷(R n) -∗ ([∗ set] γi ∈ close_tok_names,
                        ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗  ▷ (Ri n)))                     
    .

Definition own_closed_tok_post_close (γ: chan_names) (n: nat): iProp Σ := 
∃ (close_tok_names: gset gname) ,
auth_set_auth γ.(close_name) close_tok_names ∗ 
([∗ set] γi ∈ close_tok_names,
                    ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗  ▷ (Ri n))                  
.

Definition own_recv_perm (γ: chan_names) (q: Qp) (i: nat) (T:nat -> iProp Σ): iProp Σ :=
 ∃ (γi: gname),
  own_recv_counter_frag γ i q ∗ own_closed_tok_frag γ γi T .

Lemma own_chan_counter_alloc : 
⊢ |==> ∃ γ, own_chan_counter_auth γ 0 false ∗ own_chan_counter_frag γ 0 1%Qp.
  setoid_rewrite <-own_op.
  iApply own_alloc.
  apply auth_both_valid_discrete.
  split.
  - reflexivity.
  - apply Some_valid.
    apply pair_valid.
    split.
    + apply frac_valid.
      reflexivity.
    + cbv.
      done.
Qed.

Lemma own_chan_ghost_alloc (R: nat -> iProp Σ) :
⊢ |==> ∃ (γ: chan_names), 
  own_send_counter_auth γ 0 false ∗ own_send_counter_frag γ 0 1%Qp ∗ 
  own_recv_counter_auth γ 0 false ∗ own_recv_perm γ 1%Qp 0 R ∗ 
  own_closed_tok_auth γ R
.
Proof.
  iMod (own_chan_counter_alloc) as (γs) "[Hsendauth Hsendfrag]".
  iMod (own_chan_counter_alloc) as (γr) "[Hrecvauth Hrecvfrag]".
  iMod (auth_set_init (A:=gname)) as (γc) "HcloseNames".
  set (γ := {| receiver_name := γr;
                sender_name := γs;
                close_name := γc;
              |}).
  iMod (saved_pred_alloc R (DfracDiscarded)) as (γi) "#Hcp1".
              { done. }
  iMod (auth_set_alloc γi with "HcloseNames") as "[HcloseNames Hctf]".
    { set_solver. }
   set (s := {[γi]}).
  assert (s ∪ ∅ = s) as Hunion by set_solver.
   iExists γ. iFrame "#". iFrame.
   iModIntro. iIntros. iIntros "HlaterR".
   replace (s ∪ ∅) with s.
   subst s.
   rewrite -> (big_sepS_singleton _ γi) by set_solver.
   iFrame. done. 
Qed.

Definition own_close_perm (γ: chan_names) (R:nat -> iProp Σ) (n: nat): iProp Σ :=
  (R n) ∗ own_send_counter_frag γ n 1 ∗ own_closed_tok_auth γ R.

Lemma own_closed_tok_frag_split (γ : chan_names) (γi: gname) (T U :nat -> iProp Σ):
∀ (R V:nat -> iProp Σ) ,
( ∀ n,
  (V n) -∗ ((T n) ∗ (U n))) -∗ 
    (own_closed_tok_auth γ R ∗  own_closed_tok_frag γ γi V ==∗ 
    ∃ (γj γk: gname), own_closed_tok_auth γ R ∗ own_closed_tok_frag γ γj T 
    ∗ own_closed_tok_frag γ γk U
    ).
Proof.
  iIntros (R V) "Hvtu [Hauth Hfrag]". 
  unfold own_closed_tok_frag. iDestruct "Hfrag" as "[Hfrag #Hpred]".
  unfold own_closed_tok_auth. iNamed "Hauth".
  iDestruct (auth_set_elem with "[$Hownauth] [$Hfrag]") as "%".
  iMod (saved_pred_alloc_cofinite close_tok_names T DfracDiscarded)
      as (γ1) "[%Hfresh #Hj]".
    { done. }
    iMod (auth_set_alloc γ1 with "Hownauth") as "[Hownauth Hγ1]".
    { set_solver. }
  iMod (saved_pred_alloc_cofinite ({[γ1]} ∪ close_tok_names) U DfracDiscarded)
      as (γ2) "[% #Hk]".
    { done. }
    iMod (auth_set_alloc γ2 with "Hownauth") as "[Hownauth Hγ2]".
    { set_solver. }
    iMod (auth_set_dealloc with "[Hownauth Hfrag]") as "Hownauth".
    { iFrame. }
    iModIntro. iExists (γ1). iExists (γ2). iFrame "Hownauth".
    iFrame "Hγ1 Hγ2 #". iIntros. iIntros "HR".
    iDestruct ("Hauth" with "HR") as "Hauth".
    replace ((({[γ2]} ∪ ({[γ1]} ∪ close_tok_names)) ∖ {[γi]})) with 
    (({[γ2]} ∪ ({[γ1]} ∪ (close_tok_names ∖ {[γi]}))) ) by set_solver.

    rewrite -> big_sepS_union by set_solver.
    rewrite -> big_sepS_union by set_solver.
    rewrite -> big_sepS_singleton by set_solver. 
    rewrite -> big_sepS_singleton by set_solver. iFrame "#". 
    iDestruct ((big_sepS_delete _ _ γi) with "Hauth") as "[Hnewauth Hi]".
    { auto. }
    iDestruct "Hnewauth" as "(%Ri & Hnewauth & HR)".
    iDestruct (saved_pred_agree _ _ _ _ _ n  with "Hpred Hnewauth") as "H".
    iAssert (▷ (U n ∗ T n))%I with "[Hvtu HR H]" as "Hstuf".
    { iModIntro. iSpecialize ("Hvtu" $!n). iRewrite "H" in "Hvtu". 
     iDestruct ("Hvtu" with "HR") as "[$$]".  }
     iFrame. iDestruct "Hstuf" as "[$$]".
Qed.

Lemma own_recv_perm_split (γ : chan_names) (r s : Qp) (i k: nat) (T U:nat-> iProp Σ) : 
∀ (R V:nat -> iProp Σ) ,
(∀ n, (V n) -∗ ((T n) ∗ (U n))) -∗ 
own_closed_tok_auth γ R ∗ own_recv_perm γ (r + s) (i + k) V ==∗   
own_closed_tok_auth γ R ∗ own_recv_perm γ r i T ∗ own_recv_perm γ s k U.
Proof.
  intros R V. iIntros "HVSplit".
  iIntros "[Hauth Hrecv]". unfold own_recv_perm.
  iNamed "Hrecv". iDestruct "Hrecv" as "[Hrctr Hctf]".
  iDestruct ((own_closed_tok_frag_split γ γi T U)
   with "[$HVSplit] [$Hauth $Hctf] " ) as ">HXform".
  iDestruct ((recv_counter_split γ i k r s) with "Hrctr") as "Hrctr".
  iNamed "HXform". iDestruct "HXform" as "(Hcta & Hctf1 & Hctf2)".
  iDestruct "Hrctr" as "[Hrctr1 Hrctr2]".
  iModIntro. iFrame.
Qed.

End lemmas.