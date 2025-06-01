From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From New.proof.github_com.goose_lang.goose.model.channel Require Import auth_set.

Record chan_names :=
 {
    sender_name: gname;
    receiver_name: gname;
    close_name: gname;
    unbuffered_state_tracker_name: gname;
 }.

Class chanGhostStateG Σ  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}  `{!heapGS Σ}  := ChanGhostStateG {
    sender_main_saved_predG :: savedPredG Σ nat;
    close_prop_auth_setG :: auth_setG Σ gname;
    exchange_tokG :: ghost_varG Σ (bool * val);
    chan_ctrG :: inG Σ (authR (optionUR (prodR fracR natR)));
  }.

Definition chanGhostStateΣ  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}   : gFunctors :=
  #[  savedPredΣ nat; auth_setΣ gname; ghost_varΣ (bool * val); GFunctor (authR (optionUR (prodR fracR natR))) ].

#[global] Instance subG_chanGhostStateG Σ  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}  `{!heapGS Σ}  : subG chanGhostStateΣ Σ → chanGhostStateG Σ.
Proof. solve_inG. Qed.
    
Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section lemmas.
Context `{ffi_syntax}.
Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Implicit Types (v:val).  
Context  `{!chanGhostStateG Σ}.

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

Lemma chan_counter_elem (γ: gname) (n: nat) (i: nat) :
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

Lemma chan_counter_freeze (γ: gname) (n: nat) (i: nat) :
∀ frozen,
  own_chan_counter_auth γ n frozen ==∗ 
  own_chan_counter_auth γ n true.
  Proof.
    unfold own_chan_counter_auth, own_chan_counter_frag.
    intros frozen. destruct frozen.
    {
     iIntros "H". iFrame. done. 
    }
    iIntros "Hauth".
    iMod (own_update with "Hauth") as "H".
    { 
      apply auth_update_auth_persist.
    }
    {
      done.
    }
  Qed.   

Lemma chan_counter_lower (γ: gname) (n: nat) (i: nat) (q: Qp) :
 ∀ frozen,
  own_chan_counter_auth γ n frozen -∗ own_chan_counter_frag γ i q -∗ 
   ⌜i ≤ n⌝.
  Proof.
    intro frozen.
    unfold own_chan_counter_auth, own_chan_counter_frag.
    iIntros "Hauth". iIntros "Hfrag".
    iPoseProof (own_valid_2 with "Hauth Hfrag") as "%Hin".
    iPureIntro.
    destruct frozen.
    {
      apply auth_both_dfrac_valid_discrete in Hin.
      destruct Hin as (H1 & H2 & H3).
      apply Some_pair_included in H2.
      {
        destruct H2 as [H4 H5].
        rewrite Some_included_total in H5.
        apply nat_included in H5.
        done.
      }
    }
    {
      apply auth_both_dfrac_valid_discrete in Hin.
      destruct Hin as (H1 & H2 & H3).
      apply Some_pair_included in H2.
      {
        destruct H2 as [H4 H5].
        rewrite Some_included_total in H5.
        apply nat_included in H5.
        done.
      }
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

Lemma chan_counter_agree (γ: gname) (n m: nat) (p q: Qp)  :
 own_chan_counter_frag γ n p -∗  own_chan_counter_frag γ m q  -∗ 
 own_chan_counter_frag γ (n + m) (p + q).
  Proof.
    iIntros "H1". iIntros "H2".
    iDestruct ((chan_counter_split γ n m p q) with "[H1 H2]") as "H".
    {
      iFrame.
    }iFrame.
  Qed.

Lemma send_counter_elem (γ: chan_names) (n: nat) (i: nat) :
 ∀ frozen,
  own_send_counter_auth γ n frozen -∗ own_send_counter_frag γ i 1 -∗ 
   ⌜i = n⌝.
  Proof.
    apply chan_counter_elem.
  Qed.

Lemma send_counter_lower (γ: chan_names) (n: nat) (i: nat) (q: Qp) :
 ∀ frozen,
  own_send_counter_auth γ n frozen -∗ own_send_counter_frag γ i q -∗ 
   ⌜i ≤ n⌝.
  Proof.
    apply chan_counter_lower.
  Qed.

Lemma send_counter_freeze (γ: chan_names) (n: nat) :
 ∀ frozen,
  own_send_counter_auth γ n frozen  ==∗ 
  own_send_counter_auth γ n true.
  Proof.
    apply chan_counter_freeze. done.
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

Lemma send_counter_agree(γ : chan_names) (n m : nat) (p q : Qp) :
own_send_counter_frag γ n p -∗  own_send_counter_frag γ m q -∗ own_send_counter_frag γ (n + m) (p + q).
Proof.
  apply chan_counter_agree.
Qed.

Lemma recv_counter_elem (γ: chan_names) (n: nat) (i: nat) :
 ∀ frozen,
  own_recv_counter_auth γ n frozen -∗ own_recv_counter_frag γ i 1 -∗ 
   ⌜i = n⌝.
  Proof.
    apply chan_counter_elem.
  Qed.

Lemma recv_counter_lower (γ: chan_names) (n: nat) (i: nat) (q: Qp) :
 ∀ frozen,
  own_recv_counter_auth γ n frozen -∗ own_recv_counter_frag γ i q -∗ 
   ⌜i ≤ n⌝.
  Proof.
    apply chan_counter_lower.
  Qed.

Lemma recv_counter_freeze (γ: chan_names) (n: nat)  :
 ∀ frozen,
  own_recv_counter_auth γ n frozen  ==∗ 
  own_recv_counter_auth γ n true.
  Proof.
    apply chan_counter_freeze. done.
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

Lemma recv_counter_agree(γ : chan_names) (n m : nat) (p q : Qp) :
own_recv_counter_frag γ n p -∗  own_recv_counter_frag γ m q -∗ own_recv_counter_frag γ (n + m) (p + q).
Proof.
  apply chan_counter_agree.
Qed.

Definition own_closed_tok_frag (γ: chan_names) (γi: gname) (R:nat -> iProp Σ): iProp Σ :=
    auth_set_frag γ.(close_name) γi ∗ saved_pred_own γi (DfracDiscarded) R.

Definition own_closed_tok_auth (γ: chan_names) (R:nat -> iProp Σ): iProp Σ :=
  ∃ (close_tok_names: gset gname),
    "Hownauth" ∷ auth_set_auth γ.(close_name) close_tok_names ∗ 
  ∀ (n: nat),
   "HRcentral" ∷ ((R n) -∗ ([∗ set] γi ∈ close_tok_names,
                        ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗  ▷  (Ri n)))                     
    .

Definition own_closed_tok_post_close (γ: chan_names) (n: nat)
(close_tok_names: gset gname) 
: iProp Σ := 
auth_set_auth γ.(close_name) close_tok_names ∗ 
([∗ set] γi ∈ close_tok_names,
                    ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗  (Ri n))                  
.
Lemma own_closed_tok_post_close_pop_raw 
(γ: chan_names) (n: nat) (γr: gname) (Ri: nat -> iProp Σ)
(close_tok_names: gset gname): 
own_closed_tok_frag γ γr Ri ∗ 
auth_set_auth γ.(close_name) close_tok_names ∗ 
([∗ set] γi ∈ close_tok_names,
                    ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗   (Ri n))
==∗
(auth_set_auth γ.(close_name) (close_tok_names ∖ {[γr]} )) ∗ 
([∗ set] γi ∈ (close_tok_names ∖ {[γr]}),
                    ∃ Ri, saved_pred_own γi DfracDiscarded Ri ∗   (Ri n))
                    ∗ ▷   Ri n

.
Proof.
  iIntros "(H1 & H2 & H3)".
  unfold own_closed_tok_frag. iDestruct "H1" as "(Hfrag & #Hsp)".
  iDestruct (auth_set_elem with "[$H2] [$Hfrag]") as "%".
    iDestruct ((big_sepS_delete _ _ γr) with "H3") as "[Hnewauth Hi]".
    {
      done.
    }
    iNamed "Hnewauth". unfold own_closed_tok_frag. 
    iDestruct "Hnewauth" as "[Hnewauth Hri]".
    iDestruct (saved_pred_agree _ _ _ _ _ n  with "Hsp Hnewauth") as "H".
    iMod (auth_set_dealloc with "[H2 Hfrag]") as "Hownauth".
    { iFrame. }
     iFrame.
    iIntros "!>".
    iModIntro.
    iRewrite "H". done.
Qed.

Lemma own_closed_tok_post_close_pop
(γ: chan_names) (n: nat) (γr: gname) (Ri: nat -> iProp Σ)
(close_tok_names: gset gname): 
own_closed_tok_frag γ γr Ri ∗ 
own_closed_tok_post_close γ n close_tok_names
==∗
own_closed_tok_post_close γ n (close_tok_names ∖ {[γr]} ) ∗ 
▷ Ri n.
unfold own_closed_tok_post_close.
iIntros "H". iDestruct (own_closed_tok_post_close_pop_raw with "[$H]") as ">(Hs & Has & HR)". 
iFrame. done.
Qed.

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

Definition own_close_perm (γ: chan_names) (R:nat -> iProp Σ) (n: nat): iProp Σ :=
  (R n) ∗ own_send_counter_frag γ n 1 ∗ own_closed_tok_auth γ R.

Lemma own_closed_tok_frag_split (γ : chan_names) (γi: gname) (W X :nat -> iProp Σ):
∀ (R V:nat -> iProp Σ) ,
( ∀ n,
  (V n) -∗ ((W n) ∗ (X n))) -∗ 
    (own_closed_tok_auth γ R ∗  own_closed_tok_frag γ γi V ==∗ 
    ∃ (γj γk: gname), own_closed_tok_auth γ R ∗ own_closed_tok_frag γ γj W 
    ∗ own_closed_tok_frag γ γk X
    ).
Proof.
  iIntros (R V) "Hvtu [Hauth Hfrag]". 
  unfold own_closed_tok_frag. iDestruct "Hfrag" as "[Hfrag #Hpred]".
  unfold own_closed_tok_auth. iNamed "Hauth".
  iDestruct (auth_set_elem with "[$Hownauth] [$Hfrag]") as "%".
  iMod (saved_pred_alloc_cofinite close_tok_names W DfracDiscarded)
      as (γ1) "[%Hfresh #Hj]".
    { done. }
    iMod (auth_set_alloc γ1 with "Hownauth") as "[Hownauth Hγ1]".
    { set_solver. }
  iMod (saved_pred_alloc_cofinite ({[γ1]} ∪ close_tok_names) X DfracDiscarded)
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
    iAssert (▷ (W n ∗ X n))%I with "[Hvtu HR H]" as "Hstuf".
    { iModIntro. iSpecialize ("Hvtu" $!n). iRewrite "H" in "Hvtu". 
     iDestruct ("Hvtu" with "HR") as "[$$]".  }
     iFrame. iDestruct "Hstuf" as "[$$]".
Qed.

Lemma own_recv_perm_split (γ : chan_names) (r s : Qp) (i k: nat) (W X:nat-> iProp Σ) : 
∀ (R V:nat -> iProp Σ) ,
(∀ n, (V n) -∗ ((W n) ∗ (X n))) -∗ 
own_closed_tok_auth γ R ∗ own_recv_perm γ (r + s) (i + k) V ==∗   
own_closed_tok_auth γ R ∗ own_recv_perm γ r i W ∗ own_recv_perm γ s k X.
Proof.
  intros R V. iIntros "HVSplit".
  iIntros "[Hauth Hrecv]". unfold own_recv_perm.
  iNamed "Hrecv". iDestruct "Hrecv" as "[Hrctr Hctf]".
  iDestruct ((own_closed_tok_frag_split γ γi W X)
   with "[$HVSplit] [$Hauth $Hctf] " ) as ">HXform".
  iDestruct ((recv_counter_split γ i k r s) with "Hrctr") as "Hrctr".
  iNamed "HXform". iDestruct "HXform" as "(Hcta & Hctf1 & Hctf2)".
  iDestruct "Hrctr" as "[Hrctr1 Hrctr2]".
  iModIntro. iFrame.
Qed.

Definition full_exchange_token (γ: chan_names) : iProp Σ :=
  ghost_var γ.(unbuffered_state_tracker_name) 1%Qp (true, #()).

Definition exchange_token {T'} (γ: chan_names) (sender_initiated: bool) (v: T') `{!IntoVal T'} : iProp Σ :=
  ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp (sender_initiated, to_val v).

Definition sender_exchange_token {T'} `{!IntoVal T'} (γ: chan_names) (v: T') : iProp Σ :=
  exchange_token γ true v.

  Definition receiver_exchange_token (γ: chan_names) : iProp Σ :=
  ∃ dummy_v: val,
    ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp (false, dummy_v).

Lemma own_chan_ghost_alloc (R: nat -> iProp Σ) :
⊢ |==> ∃ (γ: chan_names), 
  own_send_counter_auth γ 0 false ∗ own_send_counter_frag γ 0 1%Qp ∗ 
  own_recv_counter_auth γ 0 false ∗ own_recv_perm γ 1%Qp 0 R ∗ 
  own_closed_tok_auth γ R ∗ 
  full_exchange_token γ
.
Proof.
  iMod (own_chan_counter_alloc) as (γs) "[Hsendauth Hsendfrag]".
  iMod (own_chan_counter_alloc) as (γr) "[Hrecvauth Hrecvfrag]".
  iMod (auth_set_init (A:=gname)) as (γc) "HcloseNames".
  iMod (ghost_var_alloc (true, #())) as (γst) "Htok".
  set (γ := {| receiver_name := γr;
                sender_name := γs;
                close_name := γc;
                unbuffered_state_tracker_name := γst;
              |}).
  iMod (saved_pred_alloc R (DfracDiscarded)) as (γi) "#Hcp1".
              { done. }
  iMod (auth_set_alloc γi with "HcloseNames") as "[HcloseNames Hctf]".
    { set_solver. }
   set (s := {[γi]}).
  assert (s ∪ ∅ = s) as Hunion by set_solver.
   iExists γ. iFrame "#". iFrame.
   iModIntro. iIntros. 
   iIntros "HlaterR".
   replace (s ∪ ∅) with s.
   subst s.
   rewrite -> (big_sepS_singleton _ γi) by set_solver.
   iExists R. iFrame. done. 
Qed.

Lemma exchange_token_combine {T'} `{!IntoVal T'} (γ: chan_names) :
  ∀ sender_initiated sender_initiated' (v v': T'),
  exchange_token γ sender_initiated v ∗
  exchange_token γ sender_initiated' v' ==∗
  full_exchange_token γ.
Proof.
  unfold exchange_token, full_exchange_token.
  iIntros (sender_initiated sender_initiated' v v').
  iIntros "[Htok1 Htok2]".
  iCombine "Htok1" "Htok2" as "Htok".
  iApply (ghost_var_update (true, #()) with "Htok").
Qed.

Lemma exchange_token_split {T'} `{!IntoVal T'} γ sender_initiated (v: T') :
  full_exchange_token γ ==∗ exchange_token γ sender_initiated v ∗ exchange_token γ sender_initiated v.
Proof.
  unfold full_exchange_token, exchange_token.
  iIntros "Htok".
  iMod (ghost_var_update (sender_initiated, to_val v) with "Htok") as "[Htok1 Htok2]".
  iFrame. done.
Qed.

Lemma exchange_token_agree {T'} `{!IntoVal T'} (γ : chan_names) (sender_initiated sender_initiated' : bool) (v v' : T') :
  exchange_token γ sender_initiated v -∗  exchange_token γ sender_initiated' v' -∗ ⌜ to_val v = to_val v' ∧ sender_initiated = sender_initiated' ⌝.
Proof.
  unfold exchange_token.
  iIntros "H1 H2".
  iDestruct (ghost_var_agree with "H1 H2") as "%H3".
  iPureIntro. injection H3 as -> ->. done.
Qed.

Lemma sender_exchange_token_split {T'} `{!IntoVal T'} γ (v: T') :
  full_exchange_token γ ==∗ sender_exchange_token γ v ∗ sender_exchange_token γ v.
Proof.
  unfold sender_exchange_token. apply exchange_token_split.
Qed.

Lemma receiver_exchange_token_split γ :
  full_exchange_token γ ==∗ receiver_exchange_token γ ∗ receiver_exchange_token γ.
Proof.
  unfold receiver_exchange_token, full_exchange_token.
  iIntros "Htok".
  iMod (ghost_var_update (false, #()) with "Htok") as "[Htok1 Htok2]".
  iFrame. done.
Qed.

Lemma sender_exchange_token_combine {T'} `{!IntoVal T'} γ (v v' : T') :
  sender_exchange_token γ v ∗ sender_exchange_token γ v' ==∗ full_exchange_token γ.
Proof.
  unfold sender_exchange_token.
  iIntros "[Htok1 Htok2]".
  iApply (exchange_token_combine γ true true v v' with "[Htok1 Htok2]").
  iFrame.
Qed.

Lemma receiver_exchange_token_combine γ :
  receiver_exchange_token γ ∗ receiver_exchange_token γ ==∗ full_exchange_token γ.
Proof.
  unfold receiver_exchange_token.
  iIntros "[Htok1 Htok2]".
  iDestruct "Htok1" as (dummy_v1) "Htok1".
  iDestruct "Htok2" as (dummy_v2) "Htok2".
  iApply (ghost_var_update (true, #()) with "[Htok1 Htok2]").
  iDestruct (ghost_var_agree with "[$Htok1] [$Htok2]") as "%Hag".
  iFrame. replace dummy_v1 with dummy_v2 by set_solver. done.  
Qed.

Lemma sender_exchange_token_agree {T'} `{!IntoVal T'} γ (v v' : T') :
  sender_exchange_token γ v -∗ sender_exchange_token γ v' -∗ ⌜to_val v = to_val v'⌝.
Proof.
  unfold sender_exchange_token.
  iIntros "Htok1 Htok2".
  iDestruct (exchange_token_agree γ true true v v' with "Htok1 Htok2") as "[% _]".
  iPureIntro. done.
Qed.

End lemmas.

