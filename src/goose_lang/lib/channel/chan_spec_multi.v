From Perennial.goose_lang Require Import prelude. 
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode array.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang.lib Require Import
      persistent_readonly slice slice.typed_slice  struct loop lock control map.typed_map time proph rand string.

From Perennial.goose_lang.lib.channel Require Import auth_set.
From Perennial.goose_lang.lib.channel Require Import chan_use_ctr.
From Goose.github_com.goose_lang.goose Require Import channel.


Definition in_closed_chan_state (cs: nat): bool :=
 bool_decide (cs = 5). 

Inductive chan_state: Type := 
| start
| receiver_ready
| sender_ready
| receiver_done 
| sender_done
| closed
| invalid
.

Section proof.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.
 Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}. 
 Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.

Implicit Types (v:val). 

Definition nat_to_chan_state (cs: nat) : chan_state :=
 match cs with 
 | 0 => start
 | 1 => receiver_ready
 | 2 => sender_ready
 | 3 => receiver_done
 | 4 => sender_done
 | 5 => closed
 | _ => invalid
 end
.

Definition chan_state_to_nat (cs: chan_state) : option nat:=
 match cs with 
 | start => Some 0
 | receiver_ready => Some 1
 | sender_ready => Some 2
 | receiver_done => Some 3
 | sender_done => Some 4
 | closed => Some 5
 | invalid => None
 end
.

Definition is_valid_chan_state (cs: chan_state) : bool :=
  match cs with
  | invalid => false
  | _ => true
  end.

Lemma chan_state_eq_dec: ∀ (cs1 cs2: chan_state), {cs1 = cs2} + {cs1 ≠ cs2}.
Proof.
  decide equality.
Qed.

Lemma chan_state_to_nat_inj: ∀ (cs1 cs2: chan_state),
  chan_state_to_nat cs1 = chan_state_to_nat cs2 → cs1 = cs2.
Proof.
  intros cs1 cs2 H.
  destruct cs1, cs2; simpl in H; try discriminate; auto.
Qed.


Lemma nts_zero (cs:nat) :
  cs < 6 -> nat_to_chan_state cs = closed -> cs = 5.
Proof.
  intros Hlts. intros Hnts.
  unfold nat_to_chan_state in Hnts. 
  do 5(destruct cs;first done). lia.
Qed.

Definition P (is_single_party: bool) (i:nat)
 (v: val) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)): iProp Σ :=
 if is_single_party then Psingle i v  else Pmulti v.

Definition Q (is_single_party: bool) (z: Z) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ): iProp Σ := 
if bool_decide(Z.lt z 0%Z) then True%I else (if is_single_party then Qsingle(z) else Qmulti).

Definition isUnbufferedChan (γ: chan_names) (chan_type: ty) 
  (v: val) (cs: chan_state) (is_single_party: bool) (send_count: nat) (recv_count: nat) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R:nat ->  iProp Σ): iProp Σ := 
     match cs with 
      | start => "%Hcount_eq" ∷ (⌜send_count = recv_count⌝)
      | receiver_ready => 
        "%Hcount_eq" ∷ ⌜send_count = recv_count⌝  ∗
        "HQ" ∷ Q is_single_party recv_count Qsingle Qmulti
      | sender_ready => 
        "%Hcount_eq" ∷  ⌜send_count = recv_count⌝ ∗ 
        "%Hval_ty" ∷  ⌜val_ty v chan_type⌝ ∗ 
        "HP" ∷  P is_single_party send_count v Psingle Pmulti 
      | receiver_done => 
        "%Hcountsendinc" ∷  ⌜recv_count = (send_count + 1)%nat⌝ ∗ 
        "HQ" ∷ Q is_single_party send_count Qsingle Qmulti 
      | sender_done => 
        "%Hcountsendinc" ∷ ⌜send_count = (recv_count + 1)%nat⌝ ∗
        "HP" ∷   P is_single_party recv_count v Psingle Pmulti ∗
        "%Hval_ty" ∷  ⌜val_ty v chan_type⌝ 
      | closed => "%Hcount_eq" ∷ ⌜send_count = recv_count⌝  
      | invalid => False
     end
  .

  Definition valid_elems (slice : list val) (first : u64) (count : u64) : list val :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition buff_size_inv (count : u64) (first : u64) (size : nat): iProp Σ :=
  (⌜uint.nat count <= size⌝ ∗ ⌜uint.nat first < size⌝ ∗ ⌜size > 0⌝ ∗ ⌜size + 1 < 2 ^ 63⌝)%I.

  Definition isBufferedChan (γ: chan_names) (chan_type: ty) (size: nat) (cs: chan_state) 
   (is_single_party: bool) (send_count: nat) (recv_count: nat) (count: nat) 
  (buff: Slice.t) (first:nat) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat-> iProp Σ): iProp Σ := 
    ∃ (xs: list val), 
    "%HBuffCount" ∷ ⌜(uint.Z count = (send_count - recv_count)%Z)%Z⌝ ∗
    "HBuffSlice" ∷ slice.own_slice_small buff chan_type (DfracOwn 1) xs ∗ 
    "%Hsizeinv" ∷  buff_size_inv count first size ∗ 
    "%HState" ∷ ⌜cs = start⌝ ∗ 
    "HPs" ∷ ([∗ list] i↦x ∈ valid_elems xs first count, P is_single_party (recv_count + i) x Psingle Pmulti) ∗ 
    "HQs" ∷ [∗ list] (i: nat)↦_ ∈ (seqZ 0 (size%Z - send_count%Z + recv_count%Z)), Q is_single_party (recv_count - i + count - 1) Qsingle Qmulti
  .

  Definition counters_frozen (cs: chan_state) (send_count: nat) (rec_count: nat): bool :=
  match (cs,send_count) with 
    | (closed,rec_count) => true
    |  _ => false
  end
    .

  Definition isChanInner (ch: loc) (γ: chan_names) (chan_type: ty) 
    (size: nat) (is_single_party: bool) (buff: Slice.t) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R: nat -> iProp Σ)  : iProp Σ := 
    ∃ (raw_cs: nat) (cs: chan_state)  (count: nat) (first: nat) (v: val) (send_count: nat) (recv_count: nat),
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #(W64 first) ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (counters_frozen cs send_count recv_count) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth γ recv_count (counters_frozen cs send_count recv_count) ∗ 
    "HCloseTokPostClose" ∷ 
    match cs with 
      |closed => (∃ (n:nat), own_closed_tok_post_close γ n ∗  own_send_counter_frag γ n 1 )
      |_ => True
     end 
      ∗ 
    "%Hvalidstate" ∷ ⌜ chan_state_to_nat cs = Some raw_cs ⌝   ∗  
    "HBuffUnbuff" ∷ 
    match size with 
      | 0 => isUnbufferedChan γ chan_type v cs is_single_party send_count recv_count  Psingle Pmulti
      Qsingle Qmulti R 
      | S _ => isBufferedChan γ chan_type size cs is_single_party send_count recv_count count
      buff first Psingle Pmulti Qsingle Qmulti R
    end 
  .


Definition isChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) : iProp Σ := 
    ∃ (mu_l: loc) (buff: Slice.t) ,
    "#mu" ∷ ch ↦[(Channel chan_type) :: "lock"]□ #mu_l
     ∗ 
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "#HUnBuffSlice" ∷
    match size with 
      | 0 => slice.own_slice_small buff chan_type (DfracDiscarded) []
      | S _ => True
    end 
      ∗ 
    "#Hlock" ∷ is_lock (nroot .@ "Channel") (#mu_l) (isChanInner ch γ chan_type size is_single_party buff Psingle Pmulti Qsingle Qmulti R)
.

Lemma wp_Channel__New (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
0 < size ∧ size + 1 < 2 ^ 63 ->
has_zero chan_type ->
{{{ True }}}
     NewChannelRef chan_type #size
   {{{(ch: loc) (γ: chan_names), RET #ch; 
    isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗ 
    own_recv_perm γ 1%Qp 0 R ∗
    own_closed_tok_auth γ R ∗ 
    own_send_counter_frag γ 0 1%Qp
}}}.
  Proof.
    intros Hs Hz.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.
    rewrite -wp_fupd.
   wp_apply (wp_new_free_lock). iIntros (mu) "Hlock".
   wp_pures.
   wp_apply wp_new_slice;first done.
   iIntros (slice_ptr) "Hbuffslice".
   unfold slice.own_slice. 
  wp_apply(wp_allocStruct (Channel chan_type)).
  { val_ty. }
  iIntros (ch). iIntros "Hchan".
   iNamedStruct "Hchan".
   iMod (struct_field_pointsto_persist with "lock") as "#mu".
   iMod (struct_field_pointsto_persist with "buffer") as "#buff".
   iMod (own_chan_ghost_alloc R) as (γ0) "(HSndAuth & HSndFrag & HRcvAuth & HRcvPrm & HCtf)".
   destruct size.
   {
    iDestruct "Hbuffslice" as "[Hbss Hcap]".
    iMod ((slice.own_slice_small_persist ) with "Hbss")
     as "#Hbuffslice". 
  iMod ((alloc_lock (nroot .@ "Channel") _ mu (
    (isChanInner ch γ0 chan_type
    0 is_single_party slice_ptr Psingle Pmulti Qsingle Qmulti R)
  )) with 
  "Hlock [ state $v count first HSndAuth HRcvAuth]" ) as "#Hch".
  {
    iFrame.
    iExists 0. iExists start. iExists 0. iExists 0. iExists 0. iExists 0.
    simpl. unfold counters_frozen. iFrame. done.
  }
  {
    iModIntro. iApply "HΦ". iFrame "#". iFrame. 
  }
  }
  {
    iMod ((alloc_lock (nroot .@ "Channel") _ mu (
    (isChanInner ch γ0 chan_type
    (S size) is_single_party slice_ptr Psingle Pmulti Qsingle Qmulti R)
  )) with 
  "Hlock [ state $v count first HSndAuth HRcvAuth Hbuffslice]" ) as "#Hch".
  {
    iModIntro. iFrame. iFrame "#". iExists 0. iExists start.
    iExists 0. iExists 0. iExists 0. iExists 0. unfold counters_frozen.
    iFrame. simpl. unfold isBufferedChan. simpl. iFrame "#".
    iSplitL "";first done.
    iSplitL "";first done. iFrame.
    iExists ((replicate (uint.nat (W64 (S size)))
    (zero_val chan_type))). iDestruct "Hbuffslice" as "[H1 H2]".
    unfold Q. simpl.
    rewrite -> (big_sepL_forall _ (seqZ 0 (S size - 0%nat + 0%nat))).
    {
    iFrame. 
    do 1 (iSplitL "";first done).
    unfold buff_size_inv. iFrame "%".
    simpl. unfold valid_elems.
    assert ((uint.nat (W64 0%nat) + uint.nat (W64 0%nat)) = 0).
    { word. }
    replace ((uint.nat (W64 0%nat) + uint.nat (W64 0%nat))) with 0.
    assert ((uint.nat (W64 0%nat)) = 0).
    { done. }
    replace (uint.nat (W64 0%nat)) with 0. 
    rewrite subslice_zero_length. simpl. iFrame.
    do 1 (iSplitL "";first (iPureIntro;lia)).
    do 2 (iSplitL "";first (iPureIntro;done)).
    iIntros (k x). iIntros "%Hseq". 
    rewrite bool_decide_true.
    { done. }
    { lia. }
    }
    {
      intros k. intros Z. rewrite bool_decide_true .
      { 
        simpl. intuition.
        unfold Persistent.
        rewrite persistently_True. done.
      }
      {
        lia.
      }
      }
    }
      {
        iModIntro. iApply "HΦ". iFrame "#". iFrame.
      }
  }
  Qed.

Lemma wp_Channel__Send (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
  "#HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q
}}}
     Channel__Send chan_type #ch v
{{{ RET #(); 
  Q is_single_party (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q
}}}.
  intros Hval_ty. intros Hnotnull. 
  (* Unbuffered *)
  destruct (bool_decide (size = 0%nat)) eqn:Hsize.
  {
   apply bool_decide_eq_true_1 in Hsize.
   intros Hq. wp_start. subst size. iNamed "Hpre". iNamed "HCh".
   wp_if_destruct.
   {
    wp_loadField. wp_apply wp_slice_len. 
    (wp_apply wp_ref_to);first val_ty.
    iIntros (buf) "Hbuffersize". wp_load.
     unfold slice.own_slice_small.
      iDestruct "HUnBuffSlice" as "(#Hbuffsliceptr & %Hbuffsize & %Hcap)".
      simpl in Hbuffsize.
      wp_if_destruct;first word.
      wp_apply wp_ref_to;first val_ty.
      iIntros (return_early) "return_early".
        wp_apply (wp_forBreak (λ continue,
          (
          "LoopInv_FirstLoop" ∷  ( ∃ (ret_early_b: bool) (send_index: nat), 
          "LoopInv_RetEarlyFalse" ∷ return_early ↦[boolT] #ret_early_b ∗
          "LoopInv_SendIndex" ∷  own_send_counter_frag γ send_index q ∗   
          "LoopInv_Break" ∷  (
          if continue
            then 
            ("%LoopInv_NoRetEarly" ∷ ⌜ret_early_b = false⌝ 
            ∗ "%LoopInv_SiNoInc" ∷ ⌜send_index = i⌝%I ∗ 
              "LoopInv_P" ∷ P is_single_party i v Psingle Pmulti)
          else ( 
            if ret_early_b then
              "LoopInv_Q" ∷ Q is_single_party (i) Qsingle Qmulti  ∗ 
              "%LoopInv_SiInc" ∷ ⌜send_index = (i + 1)%nat⌝%I 
            else 
              "%LoopInv_NoRecReady" ∷ ⌜send_index = i%nat⌝ )%I) 
          ) 
          ))%I
          with "[] [HP HSen return_early] [HΦ]").
          { 
           iIntros "!>". iIntros (Φ0). iIntros "IH HΦ". iNamed "IH".
            iNamed "LoopInv_FirstLoop". wp_loadField.
            wp_apply (wp_Mutex__Lock with "Hlock"). 
            iIntros "[locked inv]". wp_pures. 
            iNamed "inv". 
            unfold isUnbufferedChan. 
             wp_loadField.
              destruct cs.
              {
                iNamed "LoopInv_Break". iNamed "HBuffUnbuff".
                simpl in Hvalidstate. assert (raw_cs = 0) by set_solver.
                wp_pures. subst raw_cs.
                repeat (wp_loadField||wp_storeField).
                destruct is_single_party.
                {
                  subst q. iDestruct (send_counter_agree with "[$HSndCtrAuth] [$LoopInv_SendIndex]") as "%Hag".
                  assert (i = send_count) by set_solver.
                  replace i with send_count.
                  wp_apply (wp_Mutex__Unlock
                  with "[$Hlock chan_state value count first HSndCtrAuth HRcvCtrAuth HCloseTokPostClose LoopInv_P $locked]").
                  { unfold isChanInner. unfold isUnbufferedChan. iModIntro.
                    iExists 2%nat. iExists sender_ready. iFrame. iPureIntro.
                    done.
                  }
                  {
                   wp_pures. iModIntro. iApply "HΦ". subst ret_early_b.
                   iFrame. done. 
                  }
                }
                {
                  wp_apply (wp_Mutex__Unlock
                  with "[$Hlock chan_state value count first HSndCtrAuth HRcvCtrAuth HCloseTokPostClose LoopInv_P  $locked]").
                  { 
                    unfold isChanInner. unfold isUnbufferedChan. iModIntro.
                    iExists 2%nat. iExists sender_ready. iFrame. iPureIntro.
                    done.
                  }
                  {
                    wp_pures. iModIntro. iApply "HΦ". subst ret_early_b.
                    iFrame. done. 
                  }
                }
              }
              {
                iNamed "LoopInv_Break". iNamed "HBuffUnbuff".
                simpl in Hvalidstate. assert (raw_cs = 1) by set_solver.
                wp_pures. subst raw_cs.
                repeat (wp_loadField||wp_storeField).
                destruct is_single_party.
                {
                  subst q. iDestruct (send_counter_agree with "[$HSndCtrAuth] [$LoopInv_SendIndex] ") as "%Heq".
                  assert (i = send_count) by set_solver.
                  replace send_count with i.
                  unfold counters_frozen. unfold in_closed_chan_state. simpl.
                  iEval (replace i with send_index) in "HSndCtrAuth".
                  iDestruct ((send_counter_update γ send_index send_index) with "[$HSndCtrAuth $LoopInv_SendIndex]") as ">[HSndCtrAuth LoopInv_SendIndex]".
                    wp_apply (wp_Mutex__Unlock
                    with "[ $Hlock $locked chan_state value count first HSndCtrAuth HRcvCtrAuth LoopInv_P ]").
                    { iModIntro. unfold isChanInner. iExists 4%nat. iExists sender_done.
                      assert (recv_count = i) by set_solver.
                      replace recv_count with i by set_solver.
                      unfold counters_frozen.
                      iFrame. iPureIntro. unfold chan_state_to_nat. subst send_index.
                      (do 2 (split;first auto));first lia;val_ty.
                    } 
                    { wp_store. iModIntro. iApply "HΦ". iFrame.
                       replace recv_count with i by set_solver.
                       iFrame. iPureIntro. lia.
                    }
                  }
                  {
                    unfold counters_frozen. unfold in_closed_chan_state. simpl.
                    iDestruct ((send_counter_update γ send_count send_index) with "[$HSndCtrAuth $LoopInv_SendIndex]") as ">[HSndCtrAuth LoopInv_SendIndex]".
                    wp_apply (wp_Mutex__Unlock
                    with "[$Hlock $locked chan_state value count first HSndCtrAuth HRcvCtrAuth LoopInv_P]").
                    { 
                      iModIntro. unfold isChanInner. iExists 4%nat. iExists sender_done.
                      iFrame. iPureIntro. 
                      assert (recv_count = send_count) by set_solver.
                      replace recv_count with send_count by set_solver.
                      unfold chan_state_to_nat. 
                      (do 2 (split;first auto));first lia;val_ty.
                    }
                    { 
                      wp_store. iModIntro. iApply "HΦ". iFrame.
                      unfold Q. iFrame.
                      rewrite bool_decide_false.
                      {
                        rewrite bool_decide_false. { iFrame. iPureIntro. lia. }
                        { lia. }
                      }
                      destruct recv_count.
                      { done. }
                      { done. }
                    }
                }
              }
              {
                assert (raw_cs = 2) by set_solver.
                subst raw_cs.
                wp_pures.
                repeat (wp_loadField||wp_storeField).
                destruct is_single_party.
                {
                  subst q. iDestruct (send_counter_agree with "[$HSndCtrAuth] [$LoopInv_SendIndex] ") as "%Hag".
                  iNamed "HBuffUnbuff".
                  wp_apply (wp_Mutex__Unlock
                      with "[$Hlock  $HSndCtrAuth $HRcvCtrAuth $chan_state $value $count $first $locked HP]").
                      { 
                        iFrame. done.
                      }
                    wp_pures. iModIntro. iApply "HΦ".  iFrame.
                }
                {
                    wp_apply (wp_Mutex__Unlock
                        with "[$Hlock HBuffUnbuff HSndCtrAuth HRcvCtrAuth chan_state value count first $locked]").
                        { 
                            iFrame. done.
                        }
                      wp_pures. iModIntro. iApply "HΦ". iFrame.  
                    } 
              }
              {
                assert (raw_cs = 3) by set_solver.
                subst raw_cs.
                wp_pures.
                repeat (wp_loadField||wp_storeField).
                wp_apply (wp_Mutex__Unlock
                    with "[$Hlock HBuffUnbuff HSndCtrAuth HRcvCtrAuth chan_state value count first $locked]").
                    {
                      iFrame. done.
                    }
                  wp_pures. iModIntro. iApply "HΦ". iFrame. 
                }
                {
                assert (raw_cs = 4) by set_solver.
                subst raw_cs.
                wp_pures.
                repeat (wp_loadField||wp_storeField).
                wp_apply (wp_Mutex__Unlock
                    with "[$Hlock HBuffUnbuff HSndCtrAuth HRcvCtrAuth chan_state value count first $locked]").
                    { 
                      iFrame. done.
                    }
                  wp_pures. iModIntro. iApply "HΦ". iFrame.  
                }
                {
                  assert (raw_cs = 5) by set_solver.
                subst raw_cs.
                wp_pures. iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct Hsc]".
                iCombine "Hsc" "LoopInv_SendIndex" as "H" gives %Hvalid. 
                  apply auth_frag_op_valid_1 in Hvalid.
                  rewrite <- (Some_op (1%Qp, x) (q, send_index)) in Hvalid.
                  rewrite Some_valid in Hvalid.
                  rewrite <- (pair_op 1%Qp q x send_index) in Hvalid.
                  rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
                  rewrite frac_op in Hqvalid.
                  assert (((1 + q)%Qp ≤ 1)%Qp).
                  { done. }
                  apply Qp.not_add_le_l in H.
                  contradiction.
                }
                {
                 done. 
                }
          }
          {
            iFrame. done.
          }
          {
            iModIntro. iIntros "IH". iNamed "IH". 
            iNamed "LoopInv_FirstLoop".
            wp_pures.  
            destruct ret_early_b.
            {
              wp_load. wp_pures.
              wp_apply (wp_forBreak (λ continue,
              (
                "LoopInv_Wrapper" ∷  ( ∃ (ret_early_b: bool) (send_index: nat), 
                "LoopInv_SendIndex" ∷  (own_send_counter_frag γ send_index q) ∗   
                "HQ" ∷ Q is_single_party (i) Qsingle Qmulti ∗
                "%LoopInv_SiInc" ∷ ⌜send_index = (i + 1)%nat⌝
              )))%I
              with "[] [LoopInv_RetEarlyFalse LoopInv_SendIndex LoopInv_Break] [HΦ]").
              {    
                  iIntros "!>" (Φ0) "IH HΦ". iNamed "IH". iNamed "LoopInv_Wrapper".
                  wp_loadField.
                  wp_apply (wp_Mutex__Lock with "Hlock"). 
                  iIntros "[locked inv]". wp_pures.
                  iNamed "inv". wp_loadField.
                  wp_if_destruct.
                  {
                    wp_loadField.
                    wp_apply (wp_Mutex__Unlock
                    with "[$Hlock HBuffUnbuff HCloseTokPostClose HSndCtrAuth HRcvCtrAuth chan_state value count first $locked]").
                    { 
                     iFrame. done.
                    } 
                    {
                      wp_pures. iModIntro. iApply "HΦ". iFrame. done.  
                    }
                  }
                  {
                    wp_pures. 
                      wp_loadField.
                      assert (raw_cs = 4).
                      { 
                        unfold chan_state_to_nat in Hvalidstate.
                        destruct cs; do 7 (set_solver).
                      }
                      subst raw_cs.
                        wp_apply (wp_Mutex__Unlock
                        with "[$Hlock HBuffUnbuff HSndCtrAuth HRcvCtrAuth chan_state value count first $locked]").
                        { 
                          iFrame "%#". iFrame. unfold chan_state_to_nat in Hvalidstate.
                          assert (cs = sender_done).
                          { destruct cs; do 6 (done). }
                          subst cs. done.
                        }
                        {
                         wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                        }
                     } 
                    } 
                    { 
                      iFrame. done.
                    }
                    {
                      iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_Wrapper".
                      wp_pures. iModIntro. iApply "HΦ". iNamed "HQ". subst send_index0.
                      iFrame. unfold Q. 
                      destruct i.
                      { simpl. done. }
                      simpl. done.
                    }
            }
            {
              wp_load. wp_pures.  iNamed "LoopInv_Break".
              wp_apply (wp_forBreak (λ continue,
                (
                "LoopInv_LastLoop" ∷  ( ∃ (ret_early_b: bool) (send_index: nat), 
                "LoopInv_SendIndex" ∷  (own_send_counter_frag γ send_index q) ∗   
                "%LoopInv_Break" ∷  (if continue
                then ("%LoopInv_Cont" ∷ ⌜(send_index = i)⌝%I)
                else ("HQ" ∷ Q is_single_party (i) Qsingle Qmulti  ∗ "%LoopInv_SiInc" ∷ ⌜send_index = (i + 1)%nat⌝ )%I) 
                ) 
                ))%I
                with "[] [LoopInv_SendIndex] [HΦ]").
                { 
                  iIntros "!>". iIntros (Φ0). iIntros "IH HΦ". iNamed "IH".
                  iNamed "LoopInv_LastLoop". wp_loadField.
                  wp_apply (wp_Mutex__Lock with "Hlock"). 
                  iIntros "[locked inv]". wp_pures.
                  iNamed "inv".  iNamed "HBuffUnbuff".
                  unfold isUnbufferedChan. iNamed "HBuffUnbuff". wp_loadField.
                  wp_if_destruct.
                  {
                   assert (raw_cs = 5).
                   { 
                    unfold chan_state_to_nat in Hvalidstate.
                    do 1 (destruct cs;do 5 (set_solver)). 
                   } 
                   subst raw_cs. assert (cs = closed).
                   { destruct cs;do 5 (set_solver). }
                   subst cs.
                    wp_pures. iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct Hsc]".
                    iCombine "Hsc" "LoopInv_SendIndex" as "H" gives %Hvalid. 
                      apply auth_frag_op_valid_1 in Hvalid.
                      rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
                      rewrite Some_valid in Hvalid.
                      rewrite <- (pair_op 1%Qp q n i) in Hvalid.
                      rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
                      rewrite frac_op in Hqvalid.
                      assert (((1 + q)%Qp ≤ 1)%Qp).
                      { done. }
                      apply Qp.not_add_le_l in Hqvalid.
                      contradiction.
                   }
                   {
                    wp_pures. 
                     wp_pures. wp_loadField. 
                     wp_if_destruct.
                     {
                        wp_storeField. wp_loadField.
                        assert (raw_cs = 3%nat).
                        { destruct cs;do 7 (set_solver). }
                        assert (cs = receiver_done).
                        { destruct cs; do 7 (set_solver). }
                        subst cs.
                        iNamed "HBuffUnbuff".
                        iDestruct ((send_counter_update γ send_count i) with "[HSndCtrAuth LoopInv_SendIndex]") as ">HFupdStuff".
                        { iFrame. }
                        iDestruct "HFupdStuff" as "[HSndCtrAuth LoopInv_SendIndex]". 
                        destruct is_single_party.
                          {
                            subst q. iDestruct (send_counter_agree with "[$HSndCtrAuth] [$LoopInv_SendIndex] ") as "%Hag".
                            subst recv_count.
                              wp_apply (wp_Mutex__Unlock
                              with "[$Hlock chan_state $value $count $first $locked HSndCtrAuth HRcvCtrAuth ]").
                              {
                                iModIntro.
                                unfold isChanInner. iExists 0%nat. iExists start.
                                 iFrame. unfold counters_frozen.
                                iFrame "%#".
                                iFrame. simpl. iPureIntro.
                                do 2 split;first done.
                                lia.
                              }
                              {
                                wp_pures. iModIntro. iApply "HΦ". iFrame. 
                                
                                unfold Q. rewrite bool_decide_false.
                                {
                                  rewrite bool_decide_false.
                                  {
                                    assert (send_count = i).
                                    { lia. }
                                    subst send_count. destruct i.
                                    { iFrame. done. }
                                    iFrame. iPureIntro. exists.
                                    { done. }
                                    lia.
                                  } { lia. }
                                } lia. 
                              }
                          }
                          {
                            subst recv_count.
                            wp_apply (wp_Mutex__Unlock
                              with "[$Hlock chan_state $value $count $first HSndCtrAuth HRcvCtrAuth 
                              $locked]").
                              {
                                iModIntro. iExists 0. iExists start. iFrame. 
                                unfold counters_frozen. simpl. iFrame.
                                iPureIntro.
                                do 2 split;first done.
                                lia.
                              }
                              {
                          
                                wp_pures. iModIntro. iApply "HΦ". iFrame. 
                                unfold Q. 
                                rewrite bool_decide_false.
                                {
                                destruct i. { iFrame. done. }
                                 { 
                                  iFrame. iPureIntro. exists. { done. }
                                  lia.
                                 } 
                                } lia.
                              }
                          }
                    }
                    {
                      wp_loadField.
                      wp_apply (wp_Mutex__Unlock
                              with "[$Hlock HSndCtrAuth HRcvCtrAuth chan_state value count first 
                              HBuffUnbuff HCloseTokPostClose $locked]").
                              {
                                iFrame. done.
                              }
                              
                              {
                                wp_pures. iModIntro. iApply "HΦ". iFrame. done.
                              }
                    }
                  }
              }
            {
              iFrame. done.
            }
            {
              iModIntro. iIntros "IH". iNamed "IH". wp_pures. iApply "HΦ".
              iModIntro. iNamed "LoopInv_LastLoop". iFrame. subst send_index0.
              iFrame. destruct i.
              {
                done.
              }
              done.
            }
          }
        }
      }
     }
  {
    (* buffered channels *)
    admit.
  }
Admitted.

Lemma wp_Channel__TrySend (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  P is_single_party i v Psingle Pmulti ∗ own_send_counter_frag γ i q
}}}
     Channel__TrySend chan_type #ch v
{{{ (selected: bool), RET #selected; 
  if selected then 
    (Q is_single_party (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q)
  else 
    ( P is_single_party i v Psingle Pmulti ∗ own_send_counter_frag γ i q) 
}}}.
Admitted.

Lemma wp_Channel__Receive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__Receive chan_type #ch
{{{ (v: val) (ok: bool), RET (v,#ok); 
  (P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
  ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
    ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__ReceiveDiscardOk (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__ReceiveDiscardOk chan_type #ch
{{{ (v: val), RET (v); 
  (P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜val_ty v chan_type⌝)
    ∨  
  (own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝
    ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri 
}}}
     Channel__TryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
    ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
    ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
      ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
    )
  else 
    ( Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Admitted.

Lemma wp_Channel__Close (ch: loc) (n: nat) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  own_close_perm γ R n
}}}
     Channel__Close chan_type #ch
{{{ RET #(); True }}}.
Admitted.

End proof.
